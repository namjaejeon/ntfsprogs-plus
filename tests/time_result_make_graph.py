import sys
import csv
import pandas as pd
import matplotlib.pyplot as plt
import glob

def time_to_seconds(time_str):
    minutes, seconds = time_str.split('m ')
    seconds = seconds.replace('s', '')
    total_seconds = round(int(minutes) * 60 + float(seconds), 2)
    return total_seconds

def parse_time_v_output(output):
    results = []
    current_result = {}

    for line in output:
        line = line.strip()
        if line.startswith("Running"):
            if current_result:
                results.append(current_result)
            current_result = {'image': line.split("Running ")[1]}
        elif ':' in line:
            r = line.rsplit(":", 1)
            key = r[0].strip()
            value = r[1].strip()
            if key.strip() not in current_result:
                current_result[key.strip()] = value.strip()

    if current_result:
        results.append(current_result)

    return results

def process_time_v_results(infile, avg_data):
    global count
    with open(infile, 'r') as file:
        lines = file.readlines()

    time_v_results = parse_time_v_output(lines)

#    excel_data = [['Image', 'Elapsed Time', 'CPU Usage', 'Max RSS']]

    cnt = 0
    count += 1
    for result in time_v_results:
        image_name = result.get('image', '')
        index = -1
        cnt = cnt + 1
        for i, sublist in enumerate(avg_data):
            if sublist[0] == image_name:
                index = i
                break;

        elapsed_time = result.get('Elapsed (wall clock) time (h:mm:ss or m:ss)', '')
        elapsed_secs = time_to_seconds(elapsed_time)
        cpu_usage_percent = result.get('Percent of CPU this job got', '')
        cpu_usage = cpu_usage_percent.rsplit("%")[0]
        max_rss = result.get('Maximum resident set size (kbytes)', '')

        if index != -1:
            avg_elapsed_time = avg_data[index][1]
            avg_cpu_usage = avg_data[index][2]
            avg_max_rss = avg_data[index][3]
            avg_elapsed_time += (elapsed_secs - avg_elapsed_time) / (count)
            avg_cpu_usage += (float(cpu_usage) - avg_cpu_usage) / (count)
            avg_max_rss += (float(max_rss) - (avg_max_rss)) / (count)

            avg_data[index][1] = round(avg_elapsed_time, 2)
            avg_data[index][2] = round(avg_cpu_usage, 2)
            avg_data[index][3] = round(avg_max_rss, 2)
        else:
            avg_elapsed_time = round(elapsed_secs, 2)
            avg_cpu_usage = round(float(cpu_usage), 2)
            avg_max_rss = round(float(max_rss), 2)
            avg_data.append([image_name, avg_elapsed_time, avg_cpu_usage, avg_max_rss])

#    print(infile + "::: \n", cnt)
#    print(avg_data)
    return avg_data

def process_time_v_files(input_files):
    avg_data = []
    for ifile in input_files:
        avg_data = process_time_v_results(ifile, avg_data)
#    print(avg_data)
    return avg_data

def find_input_files(regex_filename):
    file_list = glob.glob("./" + regex_filename)
    return file_list

def plot_graph(results1, results2):
    x_values = [sublist[0] for sublist in results1]
    results1_val = [sublist[1] for sublist in results1]
    results2_val = [sublist[1] for sublist in results2]

    plt.figure(figsize=(20,12))
    bar_width = 0.35
    # x축의 위치 설정
    r1 = range(len(results1_val))
    r2 = [x + bar_width for x in r1]

    # 막대 그래프 그리기
    plt.bar(r1, results1_val, color='C0', width=bar_width, align='center', label='ntfsprogs')
    plt.bar(r2, results2_val, color='C1', width=bar_width, align='edge', label='tuxera')

    # x축 레이블 설정
    plt.xlabel('Elapsed Time')
#    plt.xticks([r + bar_width / 2 for r in range(len(results1_val))], x_values)
    plt.xticks([])
    # y축 레이블 설정
    plt.ylabel('Secs')
    # 그래프 제목 설정
    plt.title('Elapsed Time Comparison of ntfsprogs and tuxera')
    # 범례 표시
    plt.legend()
    # 그래프 보여주기
    plt.savefig("elapsed_time.png")

    results1_val = [sublist[2] for sublist in results1]
    results2_val = [sublist[2] for sublist in results2]
    plt.bar(r1, results1_val, color='C0', width=bar_width, align='center', label='ntfsprogs')
    plt.bar(r2, results2_val, color='C1', width=bar_width, align='edge', label='tuxera')
    plt.xlabel('CPU Usage')
    plt.ylabel('%')
    plt.title('CPU Usage Comparison of ntfsprogs and tuxera')
    plt.savefig("cpu_usage.png")

    results1_val = [sublist[3] for sublist in results1]
    results2_val = [sublist[3] for sublist in results2]
    plt.bar(r1, results1_val, color='C0', width=bar_width, align='center', label='ntfsprogs')
    plt.bar(r2, results2_val, color='C1', width=bar_width, align='edge', label='tuxera')
    plt.xlabel('MAX RSS')
    plt.ylabel('%')
    plt.title('MAX Memory Comparison of ntfsprogs and tuxera')
    plt.savefig("max_rss.png")

count = 0
ntfsck_input = find_input_files("*ntfsck_test_fsck.log")
ntfsck_result = process_time_v_files(ntfsck_input)
print("ntfsck result (average):")
for r in ntfsck_result:
    print(r)
ntfsck_result.sort(key = lambda x: x[0])
tuxera_input = find_input_files("*ntfsck.tuxera_test_fsck.log")
tuxera_result = process_time_v_files(tuxera_input)
print("tuxera ntfsck result (average):")
for r in tuxera_result:
    print(r)
tuxera_result.sort(key = lambda x: x[0])

plot_graph(ntfsck_result, tuxera_result)
