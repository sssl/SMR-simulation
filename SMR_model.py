#Copyright 2017 Northeastern University

#Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

#The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

#THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

#!/usr/bin/python

############## How to run ###################
# $pypy ./SMR_model.py "input_trace"	    #
# the output can be found at output.log     #
#############################################


import collections
import random
import cProfile
import sys

random.seed(17)

#round function has been used throughout the code to resolve the floating point issue

#initializes zones, bands and track size as well as zone boundaries; consecutive zones have 4KB of size difference (zone_sz_diff) and every band consists of 20 consecutive tracks
def initialize_zones_bands_and_tracks ():
        global nr_of_tracks_per_band
        global nr_of_zones
        global nr_of_tracks_per_zone
        z_sum = 0

        prev_zones_ub=0;
        nr_of_tracks_per_band = int(od_band_sz/od_track_sz)+1;
        nr_of_zones=(od_track_sz-id_track_sz)/zone_sz_diff;
        zero_to_od=(od_track_sz/zone_sz_diff)*((od_track_sz/zone_sz_diff)+1)/2;
        zero_to_id=((id_track_sz/zone_sz_diff)-1)*(id_track_sz/zone_sz_diff)/2;
        total_sz_of_single_track_zones=(zero_to_od-zero_to_id)*zone_sz_diff;
        nr_of_tracks_per_zone=int(int(device_sz/total_sz_of_single_track_zones)/20)*20;
	
        global track_sz_in_zone
        global band_sz_in_zone
        track_sz_in_zone = []
        band_sz_in_zone = []
        track_sz_in_zone.append(0)
        band_sz_in_zone.append(0)
	#zone[i][0]: zone i's lower boundary && zone[i][1]: zone i's upper boundary	
        global zone
        zone = [[0 for i in xrange (2)] for j in xrange (nr_of_zones+1)]


        for i in xrange(1,nr_of_zones+1): 
                if(i != nr_of_zones):
                        track_sz_in_zone.append(((od_track_sz/zone_sz_diff)-(i-1))*zone_sz_diff);
                        band_sz_in_zone.append(track_sz_in_zone[i]*nr_of_tracks_per_band);
                        z_sum+=nr_of_tracks_per_zone*track_sz_in_zone[i];
                        zone[i][0] = prev_zones_ub 
                        zone[i][1] =  z_sum
                else:
                        track_sz_in_zone.append(((od_track_sz/zone_sz_diff)-(i-1))*zone_sz_diff);
                        band_sz_in_zone.append(track_sz_in_zone[i]*nr_of_tracks_per_band);
                        z_sum=device_sz;
                        zone[i][0] = prev_zones_ub  
                        zone[i][1] =  z_sum
                prev_zones_ub=z_sum;

#finding the correponding track for a given address
def calc_track_number(address):
        global zone_info
        global track_info
        track_info = [-1,-1,-1]

        # pjd - do int(float) when initializing zone[][]
        # pjd - note that zone# is 1-based 
        for i in xrange(1,nr_of_zones+1): 
                if ((address-int(zone[i][0])>=0) and (address-int(zone[i][1])<0)):
                        des_z=i;
                        des_z_lb=zone[i][0];
                        des_z_ub=zone[i][1];
                        break;
	#track_info[0]: global track number for a given address && track_info[1] and track_info[2]: lower and upper bound in the calculated track  
        track_info[0]= ((des_z-1)*nr_of_tracks_per_zone)+int((address-des_z_lb)/track_sz_in_zone[des_z])+1 ;
        track_info[1]= des_z_lb+int((address-des_z_lb)/track_sz_in_zone[des_z])*track_sz_in_zone[des_z] ;
        track_info[2]= des_z_lb+(int((address-des_z_lb)/track_sz_in_zone[des_z])+1)*track_sz_in_zone[des_z];
	#zone_info: zone number
        zone_info=des_z;

#finding the correponding band for a given address
def find_band_number(address):
        global band_info
        band_info = [-1,-1,-1] #initilalize to -1, Every time the function is called, it will be changed, so there is no worries about the initial value
	#finding out which zone this address belongs to
        for i in xrange(1,nr_of_zones+1):#        for (i=1;i<=nr_of_zones;i++)
                if ((address-int(zone[i][0])>=0) and (address-int(zone[i][1])<0)):
                        des_z=i;
                        des_z_lb=zone[i][0];
                        des_z_ub=zone[i][1];
			break
	#band_info[0]:global band number for a given address && band_info[1] and band_info[2]: lower and upper bound in the calculated band
        band_info[0]= ((des_z-1)*(nr_of_tracks_per_zone/nr_of_tracks_per_band))+int((address-des_z_lb)/band_sz_in_zone[des_z])+1;
        band_info[1]= des_z_lb+int((address-des_z_lb)/band_sz_in_zone[des_z])*band_sz_in_zone[des_z];
        band_info[2]= des_z_lb+(int((address-des_z_lb)/band_sz_in_zone[des_z])+1)*band_sz_in_zone[des_z];

# returns a packet id from persistent cache's log head
def get_new_PID(trks_req,data):
        global PID # array of packet ids
        global pc_wb_log_head # log head for write backs in persistent cache
        global avail_space_in_cur_pc_wb_band
        global cache_under_pressure # is set if all 23000 map entries are in use -- gets reset when gets back to less than 22986 
        global pc_log_head # head of log in persistent cache
	global pc_log_tail # tail of log in persistent cache

	pc_log_head = round(pc_log_head,1)
	pc_log_tail = round(pc_log_tail,1)

	# data: flag bit to determine if or not a write is for new data or just a write back from cleaning
        if(data==1):
                plh=pc_log_head;
                if (pc_log_head > pc_log_tail):
                        if(round(pc_log_head+trks_req,1)>(pc_map_sz1*1.5*0.4)-0.4):
                                if(round(pc_log_tail-(pc_log_head+trks_req-pc_map_sz1*1.5*0.4+0.4),1) < pc_map_sz1*0.4*0.5  and in_the_middle_of_cleaning==0):
					clean_pc();
                        elif(round(pc_log_head-pc_log_tail+trks_req,1) > pc_map_sz1*0.4 and  in_the_middle_of_cleaning==0):
				clean_pc();
                elif (pc_log_head < pc_log_tail):
                        if(round(pc_log_tail-pc_log_head-trks_req,1) < pc_map_sz1*0.4*0.5 and  in_the_middle_of_cleaning==0):
				clean_pc();
                PID[int(round((pc_log_head*2.5),1))]=trks_req 
                if(round(pc_log_head+trks_req,1)> pc_map_sz1*1.5*0.4-0.4):
                        pc_log_head=round((pc_log_head+trks_req-pc_map_sz1*1.5*0.4+0.4),1);
                else:
                        pc_log_head=round((pc_log_head+trks_req),1);
        else:
                plh=pc_wb_log_head;
                pc_wb_log_head=(pc_wb_log_head+trks_req)%(40);
                avail_space_in_cur_pc_wb_band=(20-(pc_wb_log_head%20))*pc_track_sz;

        if(find_array_length(PID)==pc_map_sz2):
                cache_under_pressure=1;
        return plh


def find_array_length(input_array):
        array_length = 0
        for item in input_array:
                if item > 0:
                        array_length += 1
        return array_length


# makes a reference table for seeks from outer diameter to inner diameter (seek_time_OI) and vice versa (seek_time_IO)
# seek time references are read from "OI-analyzed-sorted.db" and "IO-analyzed-sorted.db"
def  initialize_seek_time_map():
        global seek_time_OI
        global seek_time_IO
        seek_time_OI = {}
        seek_time_IO = {}

        db_file = open ("OI-analyzed-sorted.db", "r")
        for line1 in db_file:
                line2 = line1.split(" ")
                value = line2[5].split("\n")
		seek_time_OI.update({line2[4]:value[0]})
        db_file.close();


        db_file = open ("IO-analyzed-sorted.db", "r")
        for line1 in db_file:
                line2 = line1.split(" ")
                value = line2[5].split("\n")
                seek_time_IO.update({line2[4]:value[0]})
        db_file.close();

# finds the closest cases in either seek_time_OI or seek_time_IO and then estimates the seek time using inter(extra)polations
def estimate_seek_time(p_track,c_track):
        min_diff=device_sz+1;
        abs_diff=abs(c_track-p_track);
        if (c_track>p_track):
                for trk_dis in seek_time_OI:
                        diff=abs(int(trk_dis)-abs_diff);
                        if diff<min_diff:
                                min_diff=diff;
                                desired_dis=trk_dis;
                return (float(seek_time_OI[desired_dis])/float(desired_dis))*abs_diff;
        else:
                for trk_dis in seek_time_IO:
                        diff=abs(int(trk_dis)-abs_diff);
                        if diff<min_diff:
                                min_diff=diff;
                                desired_dis=trk_dis;
                return (float(seek_time_IO[desired_dis])/float(desired_dis))*abs_diff;

# estimates rotational latency based on the location of previous and current tracks
def estimate_rot_lat(p_track,c_track,p_add,c_add,p_off):
        #print "p_track,c_track,p_add,c_add,p_off,op", p_track,c_track,p_add,c_add,p_off
        if (p_track == c_track):
                if(p_track==1): # both tracks on the persistent cache
                        if(abs(prev_r_pid-r_pid)<0.2):
                                if(prev_r_chunck==r_chunck):
                                        return 0;
                                else:
                                        return(full_rot_lat);
                        else:
                                if(abs((prev_r_pid%1)-(r_pid%1)) < 0.2):
                                        return(full_rot_lat);
                                elif((prev_r_pid%1)<(r_pid%1)):
                                        return((r_pid%1-prev_r_pid%1)*full_rot_lat);
                                else:
					return((1+((r_pid%1)-(prev_r_pid%1)))*full_rot_lat);
                else:
                        if(prev_r_chunck==r_chunck):
                                return(0);
                        c_t_p_a=p_add;
        else:
                if(c_track==1 or p_track==1): # if either of current or previous tracks is on the persistent cache
                	return(random.random()*full_rot_lat);
                c_t_p_a=track_info[1]+int((p_off*(track_info[2]-track_info[1]))/4096)*4096;
	# if non of tracks are on the persistent cache
        if (c_add-c_t_p_a >=147456):
                return((float((c_add-c_t_p_a))/(track_info[2]-track_info[1]))*full_rot_lat);
        elif (c_add-c_t_p_a <0):
                return(float((track_info[2]-track_info[1]+c_add-c_t_p_a))/(track_info[2]-track_info[1])*full_rot_lat);
        else:
                return(full_rot_lat);

# finds the next valid packet id
def set_tail_to_next_valid_pid():
	#Moving the pc_log_tail to the first next valid pid 	
	global pc_log_tail
	found_flag = 0
	for i in xrange (int(round((pc_log_tail*2.5))+1), pc_sz):
		if ((PID[i] % 0.4 == 0) and PID[i] > 0):
			found_index = i
			found_flag = 1
			break
	if found_flag == 0:
		for i in xrange (0,int(round(pc_log_tail*2.5))):
                	if ((PID[i] % 0.4 == 0) and PID[i] > 0):
                        	found_index = i
                        	found_flag = 1
                        	break
	if found_flag == 1:
		pc_log_tail = round((found_index / 2.5),1) #Should be divided by 2.5, as in the first place we multiplied that by 2.5
	else:
		pc_log_tail = round(pc_log_head,1)
		
	
	
# adds new writes to persistent cache
def add_io_to_pc(address,lengths):
        global band_pid_blck  
        global pid_add
        global pc_log_tail
        pid_couner = 0;
        item_to_del_found_flag = 0

        nr_d_p=1; #number of data packets
        nr_t=1; #extent map
        trks_req=(nr_d_p*0.4);
        new_pid=get_new_PID(trks_req,1);
	# breaking down write extents into 4K blocks
        for add in xrange (address,address+lengths+1,4096):
		find_band_number(add);
                bnd=band_info[0];

		if len(band_pid_blck[bnd]) > 0:
			if(add < first_add_written_in_band[bnd]):
                                        first_add_written_in_band[bnd]=add

			#check band_pid_blck[bnd] to see if it has the address or not?
			found_item_index = -1 #Initial value
			index_counter = -1;
			pid_counter = 0
			for item in band_pid_blck[bnd]:
				index_counter += 1
				if (item[1] == add):
					found_item_index = index_counter
					pid = item[0] # the pid associated with the target address
					pid_add[int(round(pid*2.5))].remove(add)
					del band_pid_blck[bnd][found_item_index]
					pid_counter = 1
					break
		
			#check if pid only occures once or not in case the address was found
			if found_item_index > -1:
				for item in band_pid_blck[bnd]:
					if (item[0] == pid ):
						pid_counter += 1
						if pid_counter > 1:
							break

			# if there is no more address associated with the target pid, we need to remove the pid 
			if pid_counter == 1:
				PID[int(round(pid*2.5,1))]=-1 #remove PID[pid] by setting the content to -1
				if(round(pid,1)==round(pc_log_tail,1)):
                                        set_tail_to_next_valid_pid()
		else:
			first_add_written_in_band[bnd]=add

		if add not in blks_in_pc[bnd]:
                        blks_in_pc[bnd].append(add);
		pid_add[int(round(new_pid*2.5))].append(add)
		band_pid_blck[bnd].append([round(new_pid,1),add])


# adds 300 ms extra latency after every 240 write operations
def  journal_update():
        global journal_delay
        global writes_since_prev_journaling
	journal_delay=300;
        writes_since_prev_journaling=0;

def reset_latencies():
        global seek_time_w, rot_lat_w, transfer_lat_w, total_lat_w, seek_time_r, rot_lat_r, transfer_lat_r, total_lat_r
        seek_time_w=0;
        rot_lat_w=0;
        transfer_lat_w=0;
        total_lat_w=0;
        seek_time_r=0;
        rot_lat_r=0;
        transfer_lat_r=0;
        total_lat_r=0;

# cleans 2 bands
def clean_pc(  ):
        global cleaned_band_in_recent_cleaning
        global band_read_delay
        global packets_collected
	global w_into_pc_delay
	global wb_to_band_delay
	global cleaning_delay
	global pck_coll_delay
	global in_the_middle_of_cleaning
	global pc_log_head
	global pc_log_tail
        print "find_array_length(PID)", find_array_length(PID)
        sz_of_involved_tracks = [-1 for i in xrange (0,300000)] # 8TiB / 30MiB = 279621 = 300000, Drivesz/Bandsz
        s_p = [-1 for i in xrange(3)]
        f_p = [-1 for i in xrange(3)]
	global cache_under_pressure
	# one band is cleaned per iteration
        for i in xrange (1, 3):
		if len(pid_add[int(round(pc_log_tail*2.5))]) == 0:
			sys.exit("nothing to clean")
		else:
			max_add = max(pid_add[int(round(pc_log_tail*2.5))]) # in case a sinmgle packet's consecutive blocks belonged to different consequent bands 
			find_band_number(max_add)
			bnd=band_info[0];

                cleaned_band_in_recent_cleaning[i]=bnd;

                calc_track_number(first_add_written_in_band[bnd]);
                first_written_track=track_info[0];
                bnd_pc_seek_time=estimate_seek_time(first_written_track,0);

                calc_track_number(band_info[2]);
                track_num_of_last_track_in_band=track_info[0];

                nr_of_tracks_to_be_read_from_band = track_num_of_last_track_in_band-first_written_track; # drive reads from the first written track to the end of band
                sz_of_involved_tracks[bnd]=track_sz_in_zone[zone_info];
                data_to_be_read_from_band=nr_of_tracks_to_be_read_from_band*sz_of_involved_tracks[bnd]; # the volume of data being read from band 
                pc_to_bnd_track_sz_ratio=float(sz_of_involved_tracks[bnd])/pc_track_sz; # the ratio of track size in persistent cache to the one in target band
                if(data_to_be_read_from_band > merge_cache_sz): # calculating the number of phases and specifying the tracks to be cleaned in each phase based on a number criteria including the size of cache dedicate in DRAM for this purpose
                        if(data_to_be_read_from_band <= 2*merge_cache_sz):
                                nr_of_phases_for_this_band=2;
                                tracks_for_first_phase=int(merge_cache_sz/sz_of_involved_tracks[bnd]);
                                tracks_for_second_phase=nr_of_tracks_to_be_read_from_band-tracks_for_first_phase;
                                tracks_for_third_phase=0;
                                if(avail_space_in_cur_pc_wb_band < tracks_for_first_phase*sz_of_involved_tracks[bnd]):
                                        avail_space_for_first_phase=avail_space_in_cur_pc_wb_band;
                                        avail_space_for_second_phase=tracks_for_second_phase*sz_of_involved_tracks[bnd];
                                elif(avail_space_in_cur_pc_wb_band < nr_of_tracks_to_be_read_from_band*sz_of_involved_tracks[bnd]):
                                        avail_space_for_first_phase=tracks_for_first_phase*sz_of_involved_tracks[bnd];
                                        avail_space_for_second_phase=avail_space_in_cur_pc_wb_band-avail_space_for_first_phase;
                                else:
                                        avail_space_for_first_phase=tracks_for_first_phase*sz_of_involved_tracks[bnd];
                                        avail_space_for_second_phase=tracks_for_second_phase*sz_of_involved_tracks[bnd];
                                avail_space_for_third_phase=0;
			else:
                                nr_of_phases_for_this_band=3;
                                tracks_for_first_phase=int(merge_cache_sz/sz_of_involved_tracks[bnd]);
				tracks_for_second_phase=int(merge_cache_sz/sz_of_involved_tracks[bnd]);
                                tracks_for_third_phase=nr_of_tracks_to_be_read_from_band-tracks_for_first_phase-tracks_for_second_phase;
                                if(avail_space_in_cur_pc_wb_band < tracks_for_first_phase*sz_of_involved_tracks[bnd]):
                                        avail_space_for_first_phase=avail_space_in_cur_pc_wb_band;
                                        avail_space_for_second_phase=tracks_for_second_phase*sz_of_involved_tracks[bnd];
                                        avail_space_for_third_phase=tracks_for_third_phase*sz_of_involved_tracks[bnd];
                                elif(avail_space_in_cur_pc_wb_band < (tracks_for_first_phase+tracks_for_second_phase)*sz_of_involved_tracks[bnd]):
                                        avail_space_for_first_phase=tracks_for_first_phase*sz_of_involved_tracks[bnd];
                                        avail_space_for_second_phase=avail_space_in_cur_pc_wb_band-avail_space_for_first_phase;
                                        avail_space_for_third_phase=tracks_for_third_phase*sz_of_involved_tracks[bnd];
                                elif(avail_space_in_cur_pc_wb_band < nr_of_tracks_to_be_read_from_band*sz_of_involved_tracks[bnd]):
                                        avail_space_for_first_phase=tracks_for_first_phase*sz_of_involved_tracks[bnd];
                                        avail_space_for_second_phase=tracks_for_second_phase*sz_of_involved_tracks[bnd];
                                        avail_space_for_third_phase=avail_space_in_cur_pc_wb_band-avail_space_for_first_phase-avail_space_for_second_phase;
                                else:
                                        avail_space_for_first_phase=tracks_for_first_phase*sz_of_involved_tracks[bnd];
                                        avail_space_for_second_phase=tracks_for_second_phase*sz_of_involved_tracks[bnd];
                                        avail_space_for_third_phase=tracks_for_third_phase*sz_of_involved_tracks[bnd];
                else:
                        nr_of_phases_for_this_band=1;
                        tracks_for_first_phase=nr_of_tracks_to_be_read_from_band;
                        tracks_for_second_phase=0;
                        tracks_for_third_phase=0;
                        if(avail_space_in_cur_pc_wb_band < tracks_for_first_phase*sz_of_involved_tracks[bnd]):
                                 avail_space_for_first_phase=avail_space_in_cur_pc_wb_band;
                                 avail_space_for_second_phase=0;
                                 avail_space_for_third_phase=0;
                        else:
                                 avail_space_for_first_phase=tracks_for_first_phase*sz_of_involved_tracks[bnd];
                                 avail_space_for_second_phase=0;
                                 avail_space_for_third_phase=0;
                get_new_PID(int((tracks_for_first_phase+tracks_for_second_phase+tracks_for_third_phase)*pc_to_bnd_track_sz_ratio),0);
		# calculating the latency for reading band in each phase
                band_read_delay[bnd,1]=tracks_for_first_phase*full_rot_lat+(2*bnd_pc_seek_time);
                if(nr_of_phases_for_this_band>=2):
                        band_read_delay[bnd,2]=tracks_for_second_phase*full_rot_lat+(2*bnd_pc_seek_time);
                        if(nr_of_phases_for_this_band==3):
                                band_read_delay[bnd,3]=tracks_for_third_phase*full_rot_lat+(2*bnd_pc_seek_time);



		pc_log_head = round(pc_log_head,1)
		pc_log_tail = round(pc_log_tail,1)
		# s_p, f_p: start point and finish point
		# calculating the number of rounds(rnd) used in the next for loop
                if(pc_log_tail < pc_log_head):
                        s_p[1]=pc_log_tail
                        f_p[1]=pc_log_head
			rnd=1;
                else:
                        s_p[1]=pc_log_tail
                        f_p[1]=round(pc_map_sz1*1.5*0.4-0.4,1)
                        s_p[2]=0
                        f_p[2]=pc_log_head
                        rnd=2;

	
	
		for r in xrange(1,rnd+1):
	                pid = s_p[r];
	                while (pid <= f_p[r]):
				item_to_del = []
				index_counter = -1;
	                        item_to_del_found_flag = 0;
				pck_coll_delay_set=0;
				pc_block_to_del = [] #stores elemetns that need to be removed from pc_block
				pid_add_to_del = [] #stores elements that need to be removed from pid_add
				if len(band_pid_blck[bnd]) == 0:
					break
				pid_rounded = round(pid,1)  
				mx_add = 0
				for element in band_pid_blck[bnd]:
					if (element[0] == pid_rounded):
						if element[1] > mx_add:
							mx_add = element[1]

				# sets packet collection delays for different phases  
				for item in band_pid_blck[bnd]:
					index_counter += 1 
					if (item[0] == pid_rounded):
						pid_add[int(round(pid*2.5))].remove(item[1])
						blks_in_pc[bnd].remove(item[1])
                	                        item_to_del_found_flag += 1; #c
                        	                item_to_del.append(index_counter);
                                        	if(pck_coll_delay_set==0):
							calc_track_number(mx_add);
        	                                     	if((track_info[0]-first_written_track)*sz_of_involved_tracks[bnd]<=avail_space_for_first_phase):
								if (bnd,1,1) not in pck_coll_delay:
									pck_coll_delay[bnd,1,1]=0
                	                                  	pck_coll_delay[bnd,1,1]+=(0.2*full_rot_lat);
                        	                             	invovled_in_phase=1;
                                	               	elif (track_info[0]-first_written_track<=tracks_for_first_phase):
								if (bnd,1,2) not in pck_coll_delay:
									pck_coll_delay[bnd,1,2]=0
                                        	              	pck_coll_delay[bnd,1,2]+=(0.2*full_rot_lat);
                                                	       	invovled_in_phase=1;
	                                              	elif ((track_info[0]-first_written_track-tracks_for_first_phase)*sz_of_involved_tracks[bnd]<=avail_space_for_second_phase):
								if (bnd,2,1) not in pck_coll_delay:
									pck_coll_delay[bnd,2,1]=0
        	                                              	pck_coll_delay[bnd,2,1]+=(0.2*full_rot_lat);
                	                               	      	invovled_in_phase=2;
                        	                  	elif (track_info[0]-first_written_track<=tracks_for_first_phase+tracks_for_second_phase):
								if (bnd,2,2) not in pck_coll_delay:
									pck_coll_delay[bnd,2,2]=0
                                	                     	pck_coll_delay[bnd,2,2]+=(0.2*full_rot_lat);
                                        	              	invovled_in_phase=2;
                                             		elif ((track_info[0]-first_written_track-tracks_for_first_phase-tracks_for_second_phase)*sz_of_involved_tracks[bnd]<=avail_space_for_third_phase):
								if (bnd,3,1) not in pck_coll_delay:
									pck_coll_delay[bnd,3,1]=0
								pck_coll_delay[bnd,3,1]+=(0.2*full_rot_lat);
        	                                              	invovled_in_phase=3;
                	                                else:
								if (bnd,3,2) not in pck_coll_delay:
									pck_coll_delay[bnd,3,2]=0
                        	                              	pck_coll_delay[bnd,3,2]+=(0.2*full_rot_lat);
                                	                      	invovled_in_phase=3;
                                        	      	pck_coll_delay_set=1;
						packets_collected[bnd,invovled_in_phase,item[1]]= 1; #The value does not matter as we just care about the key
				
				#removing the pc_blocks[bnd][add]
				#removing band_pid_blck[bnd][pid][add] and pid_add[pid][add]
				for i in xrange (len(item_to_del)-1,-1,-1):
					del band_pid_blck[bnd][item_to_del[i]]
					if i == 0: #We are working on the last item
						if(round(pid,1)==round(pc_log_tail,1)):
							set_tail_to_next_valid_pid()
						PID[int(round((pid*2.5),1))] = -1 #remove PID[pid[ by settin the content to -1                        
                                        	if (find_array_length(PID) < pc_map_sz1):
                                                	cache_under_pressure=0;

				if len(band_pid_blck[bnd]) == 0:
					del first_add_written_in_band[bnd]

				pid += 0.4
			

		if (bnd,1,1) not in pck_coll_delay:
           		pck_coll_delay[bnd,1,1]=0
		if (bnd,1,2) not in pck_coll_delay:
                        pck_coll_delay[bnd,1,2]=0
		if (bnd,2,1) not in pck_coll_delay:
                        pck_coll_delay[bnd,2,1]=0
                if (bnd,2,2) not in pck_coll_delay:
                        pck_coll_delay[bnd,2,2]=0
		if (bnd,3,1) not in pck_coll_delay:
                        pck_coll_delay[bnd,3,1]=0
                if (bnd,3,2) not in pck_coll_delay:
                        pck_coll_delay[bnd,3,2]=0
		if (bnd,1,1) not in w_into_pc_delay:
                        w_into_pc_delay[bnd,1,1]=0
		if (bnd,1,2) not in w_into_pc_delay:
                        w_into_pc_delay[bnd,1,2]=0
		if (bnd,2,1) not in w_into_pc_delay:
                        w_into_pc_delay[bnd,2,1]=0
                if (bnd,2,2) not in w_into_pc_delay:
                        w_into_pc_delay[bnd,2,2]=0
		if (bnd,3,1) not in w_into_pc_delay:
                        w_into_pc_delay[bnd,3,1]=0
                if (bnd,3,2) not in w_into_pc_delay:
                        w_into_pc_delay[bnd,3,2]=0
		# setting the latency for writing merged data into persistent cache before writing it back to data bands
	 	# checking if available space in write back log is enough for this pupose in each phase -- the operation is split into two sub-phases otherwise
		if(avail_space_for_first_phase != tracks_for_first_phase*sz_of_involved_tracks[bnd]):
        	     	w_into_pc_delay[bnd,1,1]=(avail_space_for_first_phase/float(pc_track_sz))*full_rot_lat;
 	   		w_into_pc_delay[bnd,1,2]=((tracks_for_first_phase*sz_of_involved_tracks[bnd]-avail_space_for_first_phase)/float(pc_track_sz))*full_rot_lat;
	      	else:
    		        w_into_pc_delay[bnd,1,1]=(avail_space_for_first_phase/float(pc_track_sz))*full_rot_lat;
           		w_into_pc_delay[bnd,1,2]=0;
	      	wb_to_band_delay[bnd,1]=(tracks_for_first_phase-int(nr_of_phases_for_this_band/2))*full_rot_lat+(2*bnd_pc_seek_time);
     		cleaning_delay[bnd,1]=band_read_delay[bnd,1]+pck_coll_delay[bnd,1,1]+pck_coll_delay[bnd,1,2]+w_into_pc_delay[bnd,1,1]+w_into_pc_delay[bnd,1,2]+wb_to_band_delay[bnd,1];
	     	if(nr_of_phases_for_this_band>=2):
        	   	if(avail_space_for_second_phase != tracks_for_second_phase*sz_of_involved_tracks[bnd]):
                	   	w_into_pc_delay[bnd,2,1]=(avail_space_for_second_phase/float(pc_track_sz))*full_rot_lat;
                      		w_into_pc_delay[bnd,2,2]=((tracks_for_second_phase*sz_of_involved_tracks[bnd]-avail_space_for_second_phase)/float(pc_track_sz))*full_rot_lat;
	           	else:
        	       		w_into_pc_delay[bnd,2,1]=(tracks_for_second_phase/pc_to_bnd_track_sz_ratio)*full_rot_lat;
                	  	w_into_pc_delay[bnd,2,2]=0;
	           	wb_to_band_delay[bnd,2]=(tracks_for_second_phase-int(nr_of_phases_for_this_band/3))*full_rot_lat+(2*bnd_pc_seek_time);
        	     	cleaning_delay[bnd,2]=band_read_delay[bnd,2]+pck_coll_delay[bnd,2,1]+pck_coll_delay[bnd,2,2]+w_into_pc_delay[bnd,2,1]+w_into_pc_delay[bnd,2,2]+wb_to_band_delay[bnd,2];
	            	if(nr_of_phases_for_this_band==3):
        	     		if(avail_space_for_third_phase != tracks_for_third_phase*sz_of_involved_tracks[bnd]):
                	   		w_into_pc_delay[bnd,3,1]=(avail_space_for_third_phase/float(pc_track_sz))*full_rot_lat;
                        	      	w_into_pc_delay[bnd,3,2]=((tracks_for_third_phase*sz_of_involved_tracks[bnd]-avail_space_for_third_phase)/float(pc_track_sz))*full_rot_lat;
	                     	else:
        	         	        w_into_pc_delay[bnd,3,1]=(tracks_for_third_phase/pc_to_bnd_track_sz_ratio)*full_rot_lat;
                	              	w_into_pc_delay[bnd,3,2]=0;
              			wb_to_band_delay[bnd,3]=tracks_for_third_phase*full_rot_lat+(2*bnd_pc_seek_time);
				cleaning_delay[bnd,3]=band_read_delay[bnd,3]+pck_coll_delay[bnd,3,1]+pck_coll_delay[bnd,3,2]+w_into_pc_delay[bnd,3,1]+w_into_pc_delay[bnd,3,2]+wb_to_band_delay[bnd,3];
	in_the_middle_of_cleaning=1;

# distibutes cleaning latencies among IOs being served in the middle of cleaning
def get_cleaning_delays(rw,rw_addr):
	global reads_served_from_pc
	global additional_cleaning_delay
	global max_reads_from_pc
	global in_the_middle_of_cleaning
        delay_set=0;
        rw_trk=calc_track_number(rw_addr);
	# assigns the band's entire cleaning delay to additional_cleaning_delay i.e., IOs need to wait for a band's clenaing to get done before getting served if cache is under pressure. 
        if(cache_under_pressure==1):
		for key in cleaning_delay:	
            		additional_cleaning_delay+=cleaning_delay[key];
                    	band_read_delay[key]=0;
			for key2 in w_into_pc_delay:
				if key2[0]== key[0] and key2[1] == key[1]:
                      			pck_coll_delay[key2]=0
             	                	w_into_pc_delay[key2]=0
                  	wb_to_band_delay[key]=0;

                cleaning_delay.clear();
                cleaned_band_in_recent_cleaning.clear();
                packets_collected.clear();
                in_the_middle_of_cleaning=0;
                delay_set=1;
        else: # otherwise, each IO gets affected by only the portion of cleaning process in which it gets served
		for b in xrange (1,3):
			if (b in cleaned_band_in_recent_cleaning):
                                bnds=cleaned_band_in_recent_cleaning[b];
                                cleaning_of_band=b;
                                break;

		nr_of_cleaning_phases = 0
		for key in cleaning_delay:
			if key[0] == bnds:
				nr_of_cleaning_phases += 1

		for j in xrange (1, nr_of_cleaning_phases+1):
                        if(cleaning_delay[bnds,j] >0):
				rw_addr_found_flag = 0
				for key in packets_collected:
					if key[0] == bnds and key[1] == j and key[2] == rw_addr:
						rw_addr_found_flag = 1
						break
                                if (band_read_delay[bnds,j] != 0):
                                        additional_cleaning_delay=band_read_delay[bnds,j];
                                        if(pck_coll_delay[bnds,j,1]!=0 or pck_coll_delay[bnds,j,2]!=0):
                                                max_reads_from_pc[1]=int(band_read_delay[bnds,j]*(pck_coll_delay[bnds,j,1]/(pck_coll_delay[bnds,j,1]+pck_coll_delay[bnds,j,2])));
                                                max_reads_from_pc[2]= int(band_read_delay[bnds,j]-max_reads_from_pc[1]);
                                        cleaning_delay[bnds,j]-=band_read_delay[bnds,j];
                                        band_read_delay[bnds,j]=0;
                                        delay_set=1;
                                        break;
				# reads in the middle of packet collection phase see no additional delays if they are for the same blocks being cleaned 
                                elif (pck_coll_delay[bnds,j,1] != 0): 
					if(rw==0 and  rw_addr_found_flag == 1 and max_reads_from_pc[1] >0):
                                                additional_cleaning_delay=0;
                                                reads_served_from_pc += 1;
                                                if(reads_served_from_pc==max_reads_from_pc[1]):
                                                        pck_coll_delay[bnds,j,1]=0;
                                                        cleaning_delay[bnds,j]-=pck_coll_delay[bnds,j,1];
                                                        reads_served_from_pc=0;
                                                delay_set=1;
                                                break;
                                        else:
                                                if(max_reads_from_pc[1]>0):
                                                        additional_cleaning_delay=(1-(reads_served_from_pc/max_reads_from_pc[1]))*pck_coll_delay[bnds,j,1];
                                                cleaning_delay[bnds,j]-=pck_coll_delay[bnds,j,1];
                                                pck_coll_delay[bnds,j,1]=0;
                                                reads_served_from_pc=0;
                                                delay_set=1;
                                                break;
				elif (w_into_pc_delay[bnds,j,1] != 0):
                                        additional_cleaning_delay=w_into_pc_delay[bnds,j,1];
                                        cleaning_delay[bnds,j]-=w_into_pc_delay[bnds,j,1];
                                        w_into_pc_delay[bnds,j,1]=0;
                                        delay_set=1;
                                        break;
                                elif (pck_coll_delay[bnds,j,2] != 0):
                                        if(rw==0 and rw_addr_found_flag == 1 and max_reads_from_pc[2]>0 ):
                                                additional_cleaning_delay=0;
                                                reads_served_from_pc += 1
                                                if(reads_served_from_pc==max_reads_from_pc[2]):
                                                        pck_coll_delay[bnds,j,2]=0;
                                                        cleaning_delay[bnds,j] -= pck_coll_delay[bnds,j,2];
                                                        reads_served_from_pc=0;
                                                delay_set=1;
                                                break;
                                        else:
                                                if(max_reads_from_pc[2] > 0):
                                                        additional_cleaning_delay=(1-(reads_served_from_pc/max_reads_from_pc[2]))*pck_coll_delay[bnds,j,2];
                                                cleaning_delay[bnds,j]-=pck_coll_delay[bnds,j,2];
                                                pck_coll_delay[bnds,j,2]=0;
                                                reads_served_from_pc=0;
                                                delay_set=1;
                                                break;
                                elif (w_into_pc_delay[bnds,j,2] !=0):
                                        additional_cleaning_delay=w_into_pc_delay[bnds,j,2];

                                        cleaning_delay[bnds,j]-=w_into_pc_delay[bnds,j,2];
                                        w_into_pc_delay[bnds,j,2]=0;
                                        delay_set=1;
                                        break;
                                elif (wb_to_band_delay[bnds,j] !=0):
                                        additional_cleaning_delay=wb_to_band_delay[bnds,j];
                                        cleaning_delay[bnds,j]=0;
                                        wb_to_band_delay[bnds,j]=0;
					to_del_cleaning_delay = []
					to_del_packets_collected = []
                                        if(j==nr_of_cleaning_phases):
						for key in cleaning_delay: #delete cleaning_delay[bnds];
							if key[0] == bnds:
								to_del_cleaning_delay.append(key)
						for element in to_del_cleaning_delay:
							del cleaning_delay[element]
						for key in packets_collected:
							if key[0] == bnds:
                                                                del packets_collected[key] #delete packets_collected[bnds];
								break
                                                if(len(cleaned_band_in_recent_cleaning)==1):
                                                        in_the_middle_of_cleaning=0;
                                                del cleaned_band_in_recent_cleaning[cleaning_of_band];
                                        delay_set=1;
                                        break;
                                else:
                                        sys.exit("Cleaning Delay Inconsistency");



device_sz=5000980856832;
rpm=5980;
max_io_sz=524288;
merge_cache_sz=14680064; #DRAM space dedicated for data reading during cleaning
cur_time=0;
journal_update_period=240;
seek_time_w=0;rot_lat_w=0; transfer_lat_w=0; total_lat_w=0;
seek_time_r=0;rot_lat_r=0; transfer_lat_r=0; total_lat_r=0;
writes_since_prev_journaling=0;
total_writes=0;

od_track_sz=1900544; #track size at outer diameter 1.8125 MiB 
id_track_sz=987136;  #track size at inner diameter 0.941 MiB
od_band_sz=36*(2**20);   #band size at outer diameter
id_band_sz=18*(2**20);   #band size at inner diameter

pc_track_sz=od_track_sz;
pc_band_sz=od_band_sz;

zone_sz_diff=4096; # the track size di

pc_log_tail=0
pc_log_head=0
pc_wb_log_head=0;
journal_delay=0 # adds journaling delay of ~300ms after every 240 writes
in_the_middle_of_cleaning=0; #flag to check if the cleaning process is in run

pc_map_sz1 = 22986 # mapping table size "number of entries that triggers cleaning"
pc_map_sz2 = 23000 # real mapping table size
pc_sz = int(pc_map_sz1 * 1.5) # persistent cache size with 50% of OP based on our observations

PID  = [-1 for j in xrange (0,pc_sz)] #persistent cache log
first_add_written_in_band = {}
blks_in_pc= [[0 for i in xrange (0)] for j in xrange(300000)] # a list of lists. each row is dedicated to a band. each column of a row stores an address belongs to that band
pid_add = [[0 for i in xrange (0)] for j in xrange(pc_sz)] # a list of lists. each row is dedicated to a pid. each column of a row stores an address belongs to that pid
band_pid_blck = [[0 for i in xrange (0)] for j in xrange(300000)] #a list of lists. each row is dedicated to a fixed band number. each column of a row stores a pair of (pid, address) belongs to that band.

cleaning_delay = collections.OrderedDict() #total delay per band cleaning
band_read_delay = {} # delay of reading a band's data
pck_coll_delay = {} # delay of reading updates(writes) of the band currently being cleaned
w_into_pc_delay = {} # delaly of writing the merged data from band and pc into pc
wb_to_band_delay = {} # delay of writing back band's updated data to its original place

cleaned_band_in_recent_cleaning = {}
packets_collected = {}

reads_served_from_pc = 0; # reads served from pc while the same band is being cleaned and the cleaning is in packet collection phase
max_reads_from_pc = [-1 for i in xrange (0,3)] # max servable reads from persistent cache

cur_track=1; 
cur_time=0; 
half_rot_lat=60000/float(rpm)/2;
full_rot_lat=60000/float(rpm)

r_pid, prev_r_pid, prev_r_chunck, r_chunck, cur_off, cur_add=0, 0, 0, 0, 0, 0; # used in rotational latency estimations

initialize_seek_time_map();
initialize_zones_bands_and_tracks();

avail_space_in_cur_pc_wb_band = od_band_sz; # the space avialble in pc's current band dedicated to writing of merged data before write back to band

Address = set()
in_file = open(sys.argv[1], "r")
out_file = sys.stdout
in_file_content = in_file.readlines()

#import pdb
lineno = 1

####### main loop #######
for line in in_file_content:
	line_splitted = line.split()
	if (writes_since_prev_journaling%journal_update_period==0):
                if writes_since_prev_journaling > 0:
                        journal_update()

                        #        if lineno == 12:
                        #                pdb.set_trace()
        if (line_splitted[1]=="read"):
                offset,bytes=map(int,line_splitted[2:]) # pjd - minor optimization
                # pjd - wonder if 512K is right - READ/WRITE DMA limited to 128K
                if (bytes>max_io_sz): # breaks down the io extent in case of being greater than 512K
			for i in xrange(offset, offset+bytes+1-max_io_sz, max_io_sz):
				Address.add((i, max_io_sz))
                                if (i+max_io_sz+max_io_sz+0 > offset+bytes):
                                        Address.add((i+max_io_sz,offset+bytes-(i+max_io_sz)))
	                               	break;
                else:
                        Address.add((offset,bytes)) 
		add_list = [] 
		for add_item in Address:
			a = add_item[0]
			additional_cleaning_delay=0;
                        additional_journal_delay=0;
			if add_item[0] not in add_list:
				add_list.append(add_item[0])
				for add_item2 in Address:
					l = add_item2[1]
					if add_item2[0] == a:
		                                r_chunck=-1;
                		                prev_r_chunck=-1;
						for addr in xrange(a+0, a+l+0+1, 4096):
                		                        r_chunck=a;
                                		        find_band_number(addr);
		                                        bnd=band_info[0];
							found_band_addr_flag2=0 # set to 1
                                                        # if addr is already in PC
							if addr in blks_in_pc[bnd]:
                		                        	calc_track_number(0);
                                		           	track_to_seek_r=track_info[0];
								for pid_add_pair in band_pid_blck[bnd]:
									if pid_add_pair[1] == addr:
                                                		       		r_pid=pid_add_pair[0]+0;
                                                                		break;
                                		             	cur_add=0;
                                                		cur_off=r_pid%1;
								found_band_addr_flag2 = 1
                		                        if found_band_addr_flag2==0:
                                                		calc_track_number(addr);
		                                                track_to_seek_r=track_info[0];
                		                                cur_add=addr;
                                		                cur_off=int((addr-track_info[1])/4096)/float(track_info[2]-track_info[1]);      
                		                        if (abs(cur_track-track_to_seek_r)>0):
                                                		seek_time_r+=estimate_seek_time(cur_track,track_to_seek_r);
                		                        else:
                                                		seek_time_r=0;
                		                        rot_lat_r+=estimate_rot_lat(cur_track,track_to_seek_r,cur_add,addr,cur_off);
                                		        prev_r_pid=r_pid;
		                                        prev_r_chunck=r_chunck;
                		                        cur_track=track_to_seek_r;
                                		        transfer_lat_r+=60000/float(rpm)*(4096/float(track_info[2]-track_info[1]));
                		                if(in_the_middle_of_cleaning==1):
		                                        get_cleaning_delays(0,a);
		del add_list
                total_lat_r=seek_time_r+transfer_lat_r+rot_lat_r+additional_cleaning_delay;
                cur_time+=total_lat_r;
		pid_add_cnt = 0

                print >> out_file, cur_time, total_lat_r, seek_time_r, transfer_lat_r, rot_lat_r, additional_cleaning_delay
                Address.clear();
                reset_latencies();
                if(in_the_middle_of_cleaning==0):
                        if (round(pc_log_head,1) > round(pc_log_tail,1)):
                                if(round(pc_log_head-pc_log_tail,1) > (pc_map_sz1-1)*0.4): 
					clean_pc();
                        elif (round(pc_log_head,1) < round(pc_log_tail,1)):
                                if(round(pc_log_tail-pc_log_head,1) < (pc_map_sz1-1)*0.4*0.5): 
					clean_pc();
        elif (line_splitted[1]=="write"):
                offset,bytes=map(int,line_splitted[2:])
                additional_cleaning_delay=0;
                additional_journal_delay=0;
                if(bytes %max_io_sz == 0):
                        pkts_to_write=(bytes/max_io_sz); #number of packets being written in the persistent cache in this write
                else:
                        pkts_to_write=int(bytes/max_io_sz)+1;
                last_i=0
                if(bytes>max_io_sz):
			for i in xrange(offset, offset+bytes+1, max_io_sz):
                                add_io_to_pc(i,max_io_sz);
                                if(in_the_middle_of_cleaning==1):
                                        get_cleaning_delays(1,i)
                                if(journal_delay>0):
                                        additional_journal_delay+=journal_delay;
                                        journal_delay=0;
                                last_i=i;
                                transfer_lat_w+=2.4*full_rot_lat*pkts_to_write;
                        if(bytes%max_io_sz!=0):
				add_io_to_pc(last_i+max_io_sz,l-(last_i+max_io_sz));
                                if(in_the_middle_of_cleaning==1):
                                        get_cleaning_delays(1,last_i+max_io_sz);
                                if(journal_delay>0):
                                        additional_journal_delay+=journal_delay;
                                        journal_delay=0;
                                transfer_lat_w+=2.4*full_rot_lat*pkts_to_write;
                else:
                        add_io_to_pc(offset,bytes);
                        if(in_the_middle_of_cleaning==1):
                                get_cleaning_delays(1,offset);
                        if(journal_delay>0):
                                additional_journal_delay+=journal_delay;
                                journal_delay=0;
                        transfer_lat_w=2.4*full_rot_lat*pkts_to_write;
                calc_track_number(0);
                track_to_seek_w=track_info[0];
                if (abs(cur_track-track_to_seek_w)>0):
                        seek_time_w=estimate_seek_time(cur_track,track_to_seek_w);
                        rot_lat_w=estimate_rot_lat(cur_track,1,cur_add,0,1);
                else:
                        seek_time_w=0;
                        rot_lat_w=0.7;
                total_lat_w=seek_time_w+rot_lat_w+transfer_lat_w+additional_cleaning_delay+additional_journal_delay;
                cur_time+=total_lat_w;
                cur_add=0;
                cur_off=0;
		pid_add_cnt = 0
                print >> out_file, cur_time, total_lat_w, seek_time_w, rot_lat_w, transfer_lat_w, additional_cleaning_delay, additional_journal_delay
                reset_latencies();
                total_writes=total_writes+pkts_to_write;
                writes_since_prev_journaling=writes_since_prev_journaling+pkts_to_write;
                cur_track=track_to_seek_w;
        lineno += 1

