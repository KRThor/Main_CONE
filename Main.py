from multiprocessing import Queue as MQueue
from tabulate import tabulate
import numpy as np
import py_compile
import threading
import traceback
import datetime
import pickle
import socket
import shutil
import time
import stat
import uuid
import json
import glob
import cv2
import git
import sys
import os
import re

from tkinter import END, messagebox
from tkcalendar import Calendar
from PIL import Image, ImageTk, ImageDraw, ImageFont
import tkinter as tk

# from pymodbus.client.sync import ModbusTcpClient  # 실제 적용시 사용
from pymodbus.client import ModbusTcpClient  # 테스트용

from lib.config import get_line_config, create_result_dict, create_bool_dict
from lib.email_sender import send_excel_report_with_context
from lib.excel_report_generator import ExcelReportGenerator
from lib.log import LogManager
from lib.mysql import MySql

# ▶ 메인 프레임 클래스
class MainFrame(tk.Frame):
    def __init__(self, master=None):
        super().__init__(master)
        self.master = master

        self.bg_image = ImageTk.PhotoImage(file=f"bg/{line_type}/main_bg.png")
        self.client_connect_complete_image = ImageTk.PhotoImage(file=f"bg/common/connecticon.png")
        self.client_connect_fail_image = ImageTk.PhotoImage(file=f"bg/common/connecticon_fail.png")
        self.ok_sign_image = ImageTk.PhotoImage(file=f"bg/common/OK.png")
        self.ng_sign_image = ImageTk.PhotoImage(file=f"bg/common/NG.png")
        self.main_frame_off_btn = ImageTk.PhotoImage(file=f"bg/common/main_frame_off_btn.png")
        self.camera_ng_count_check_btn = ImageTk.PhotoImage(file=f"bg/common/camera_ng_count_check_btn.png")
        self.ng_log_checking_popup_image = ImageTk.PhotoImage(file=f"bg/common/ng_log_checking_popup.png")

        # 클라이언트 연결 상태 깜빡임 관련 변수
        self.client_blink_states = [False] * client_num  # 각 클라이언트의 깜빡임 상태
        self.client_blink_timers = [None] * client_num   # 각 클라이언트의 깜빡임 타이머
        self.client_connection_states = ['disconnected'] * client_num  # 각 클라이언트의 연결 상태: 'disconnected', 'connecting', 'failed', 'connected'
        self.client_connecting_timers = [None] * client_num  # 각 클라이언트의 connecting 타임아웃 타이머
        self.connecting_timeout = 20000  # connecting 상태 타임아웃 (20초)
        
        # 클라이언트 상태 팝업 관련 변수
        self.client_status_popup = None  # 클라이언트 상태 팝업 창
        self.client_load_failures = {}  # 클라이언트별 로드 실패 정보 저장

        self.reset_time = model_info.get("reset_info", {}).get("time", "1992-08-22 00:00:00")  # 로그 초기화 시간

        self.master.attributes("-fullscreen", True)
        self.master.bind("<F11>", lambda event: self.master.attributes("-fullscreen", not self.master.attributes("-fullscreen")))
        self.master.bind("<Escape>", lambda event: self.master.attributes("-fullscreen", False))
        self.create_widgets()

    def create_widgets(self):
        self.grid(row=0, column=0)
        self.main_canvas = tk.Canvas(self, width=1920, height=1080)
        self.BG = self.main_canvas.create_image(0, 0, image=self.bg_image, anchor="nw")

        self.main_frame_btn_place = self.main_canvas.create_image(90, 977, image=self.main_frame_off_btn, anchor="nw", state="hidden")
        self.camera_ng_count_check_btn_place = self.main_canvas.create_image(830, 977, image=self.camera_ng_count_check_btn, anchor="nw", state="hidden")

        # 화면 표시 폰트 서식
        self.font = ('Malgun Gothic', 16, 'bold')
        self.result_log_font = ('Malgun Gothic', 10)

        # 클라이언트 연결 상태 표시
        self.client_connect_complete_place_list = [None] * client_num
        for i in range(client_num):
            if i < 3:
                self.client_connect_complete_place_list[i] = self.main_canvas.create_image(1071+(i*128), 31, 
                                                                                           image=self.client_connect_complete_image, 
                                                                                           anchor="nw", state="hidden", tags=f"client_status_{i}")
            else:
                self.client_connect_complete_place_list[i] = self.main_canvas.create_image(1071+((i-3)*128), 73, 
                                                                                           image=self.client_connect_complete_image, 
                                                                                           anchor="nw", state="hidden", tags=f"client_status_{i}")
    
        # 이미지 출력 공간 선언
        self.show_image_list = [None] * client_num 
        self.show_place_list = [None] * client_num
        for i in range(client_num):
            if i < 3:
                self.show_place_list[i] = self.main_canvas.create_image(96+(i*441), 140, image='', anchor="nw", state="hidden")
            else :
                self.show_place_list[i] = self.main_canvas.create_image(96+((i-3)*441), 553, image='', anchor="nw", state="hidden")
        
        # OK, NG 표시 출력 공간 선언
        self.ok_sign_place_list = [None] * client_num
        self.ng_sign_place_list = [None] * client_num
        for i in range(client_num):
            if i < 3:
                self.ok_sign_place_list[i] = self.main_canvas.create_image(91+(i*441), 444, image = self.ok_sign_image, anchor="nw", state="hidden")
                self.ng_sign_place_list[i] = self.main_canvas.create_image(311+(i*441), 444, image = self.ng_sign_image, anchor="nw", state="hidden")
            else :
                self.ok_sign_place_list[i] = self.main_canvas.create_image(91+((i-3)*441), 857, image = self.ok_sign_image, anchor="nw", state="hidden")
                self.ng_sign_place_list[i] = self.main_canvas.create_image(311+((i-3)*441), 857, image = self.ng_sign_image, anchor="nw", state="hidden")

        # 모델 이름 저장 변수
        self.model_name_place = self.main_canvas.create_text(1646, 163, text = 'None', font = self.font, fill='white', anchor='center')

        # 상태 표시 엔트리
        self.state_entry = tk.Entry(self.main_canvas, font=self.font, width=27, bg='#2a5565', fg='white')
        self.state_entry_window = self.main_canvas.create_window(1596, 237, window=self.state_entry)

        # 카운트 저장 변수 선언
        self.total_count, self.ok_count, self.ng_count = DB.read_count()
        self.total_count_place = self.main_canvas.create_text(1510, 389, text = self.total_count, font = self.font, fill='white', anchor='center')
        self.ok_count_place = self.main_canvas.create_text(1656, 389, text = self.ok_count, font = self.font, fill ='#51fc59', anchor='center') 
        self.ng_count_place = self.main_canvas.create_text(1787, 389, text = self.ng_count, font = self.font, fill ='#ec5151', anchor='center') 

        # 중대 불량 이력 리스트
        self.critical_ng_log_list_click = False
        self.critical_ng_log = tk.Listbox(self.main_canvas, fg='white', bg='#2a5565', font=self.result_log_font, exportselection=False, selectmode='single')
        self.critical_ng_log.place(x=1427, y=481, width=206, height=556) 
        self.critical_ng_log_scrollbar = tk.Scrollbar(self.main_canvas, bg='#2a5565', orient="vertical")
        self.critical_ng_log_scrollbar.config(command=self.critical_ng_log.yview)
        self.critical_ng_log_scrollbar.place(x=1618, y=481, width=15, height=556)
        self.critical_ng_log.config(yscrollcommand=self.critical_ng_log_scrollbar.set)
        self.critical_ng_log.bind('<<ListboxSelect>>', self.on_log_select)
        self.critical_ng_log.bind('<Up>', self.on_log_key)
        self.critical_ng_log.bind('<Down>', self.on_log_key)

        # 일반 불량 이력 리스트
        self.normal_ng_log_list_click = False
        self.normal_ng_log = tk.Listbox(self.main_canvas, fg='white', bg='#2a5565', font=self.result_log_font, exportselection=False, selectmode='single')
        self.normal_ng_log.place(x=1660, y=481, width=206, height=556) 
        self.normal_ng_log_scrollbar = tk.Scrollbar(self.main_canvas, bg='#2a5565', orient="vertical")
        self.normal_ng_log_scrollbar.config(command=self.normal_ng_log.yview)
        self.normal_ng_log_scrollbar.place(x=1851, y=481, width=15, height=556)
        self.normal_ng_log.config(yscrollcommand=self.normal_ng_log_scrollbar.set)
        self.normal_ng_log.bind('<<ListboxSelect>>', self.on_log_select)
        self.normal_ng_log.bind('<Up>', self.on_log_key)
        self.normal_ng_log.bind('<Down>', self.on_log_key)

        self.ng_log_checking_popup = self.main_canvas.create_image(1193, 977, image=self.ng_log_checking_popup_image, anchor="nw", state="hidden")

        self.ng_log_checking = False  # 불량 로그 확인 여부
        self.ng_statistics_mode = False  # 카메라별 불량 수량 확인 모드
        
        self.main_canvas.bind("<Button-1>", self.main_btn)
        self.main_canvas.pack()

    def save_info_json(self, new_model_info):
        """모델 정보 저장"""
        global model_info
        with open('config/info.json', 'w', encoding='utf-8') as f:
            json.dump(new_model_info, f, ensure_ascii=False, indent=4)
        
        model_info = new_model_info
        
    def read_current_state(self):
        """현재 상태 코멘트 읽기"""
        current_state = model_info["models"][MB.model_name]["current_status"]
        self.state_entry.delete(0, END)
        self.state_entry.insert(0, current_state)

    def save_current_state(self):
        """현재 상태 코멘트 저장"""
        result = messagebox.askyesno("확인", "현재 상태를 저장하시겠습니까?")
        if result:
            current_state = self.state_entry.get()
            model_info["models"][MB.model_name]["current_status"] = current_state
            self.save_info_json(model_info)
            SS.send_json()
            print("current state saved")
    
    def on_closing(self):
        """프로그램 종료 확인"""
        result = messagebox.askyesno("확인", "프로그램을 종료하시겠습니까?")
        if result:
            sys.exit(0)

    def main_btn(self, event):
        """메인 버튼 클릭 이벤트"""
        x = event.x
        y = event.y
        
        if 1870 < x < 1912 and 11 < y < 53:
            print("program exit")
            self.on_closing()
        
        elif 1783 < x < 1875 and 205 < y < 269:
            print("current state change")
            self.save_current_state()
        
        elif 1189 < x < 1377 and 972 < y < 1055:
            if self.ng_log_checking:
                print("ng log checking popup close")
                self.clear_log_images()
        
        # 메인 화면 버튼 클릭
        elif 89 < x < 271 and 976 < y < 1051:
            print("main frame open")
            if MB.model_name:
                if self.ng_statistics_mode:
                    self.toggle_ng_statistics_mode()
                
                if self.ng_log_checking:
                    self.clear_log_images()
        
        # 이력 조회 버튼 클릭
        elif 274 < x < 456 and 976 < y < 1051:
            print("history frame open")
            HF.tkraise()
        
        # 관리자 모드 클릭
        elif 459 < x < 641 and 976 < y < 1051:
            print("admin frame open")
            AF.tkraise()
        
        # 최근 불량 확인 버튼 클릭
        elif 644 < x < 826 and 976 < y < 1051:
            print("recent ng check frame open")
            RN.tkraise()
        
        # 카메라별 불량 수량 확인
        elif 829 < x < 1011 and 976 < y < 1051:
            print("camera ng count check")
            if self.ng_log_checking:
                self.clear_log_images()

            self.toggle_ng_statistics_mode()
        
        elif 0 < x < 100 and 0 < y < 100:  # 테스트용
            print("start - test")
            HW.reset_variables()
            SS.send_msg_to_client("start")
        
        # 클라이언트 상태 영역 클릭 처리
        elif self.is_client_status_click(x, y):
            client_idx = self.get_client_index_from_click(x, y)
            if client_idx is not None:
                self.show_client_status_popup(client_idx)

    def update_count(self, final_station_dict):
        """카운트 업데이트"""
        count_type = 'OK'
        for client_id, result in final_station_dict.items():
            label = result['label']
            if (label is None) or ('OK' not in label):
                count_type = 'NG'
                break

        DB.update_count(count_type)
        self.total_count, self.ok_count, self.ng_count = DB.read_count()
        self.main_canvas.itemconfig(self.total_count_place, text=self.total_count)
        self.main_canvas.itemconfig(self.ok_count_place, text=self.ok_count)
        self.main_canvas.itemconfig(self.ng_count_place, text=self.ng_count)
    
    def count_reset(self, reset_type):
        """카운트 리셋
        Args:
            reset_type (str): 리셋 타입 (RESET, NG_RESET)
                RESET: 전체 리셋
                NG_RESET: 불량 카운트만 리셋
        """
        DB.update_count(reset_type)
        self.total_count, self.ok_count, self.ng_count = DB.read_count()
        self.main_canvas.itemconfig(self.total_count_place, text=self.total_count)
        self.main_canvas.itemconfig(self.ok_count_place, text=self.ok_count)
        self.main_canvas.itemconfig(self.ng_count_place, text=self.ng_count)

    def switch_ok_ng_sign(self, label, display_idx):
        """OK, NG 표시 스위치"""
        label = str(label).upper()
        if label == 'NONE':
            self.main_canvas.itemconfig(self.ok_sign_place_list[display_idx], state='hidden')
            self.main_canvas.itemconfig(self.ng_sign_place_list[display_idx], state='hidden')
        elif 'OK' not in label:
            MF.main_canvas.itemconfig(MF.ok_sign_place_list[display_idx], state='hidden')
            MF.main_canvas.itemconfig(MF.ng_sign_place_list[display_idx], state='normal')
        else:
            MF.main_canvas.itemconfig(MF.ok_sign_place_list[display_idx], state='normal')
            MF.main_canvas.itemconfig(MF.ng_sign_place_list[display_idx], state='hidden')
    
    def update_result_log(self):
        """검사 결과 로그 업데이트"""
        results_table = ['critical_results', 'normal_results']

        for table in results_table:
            rows = DB.read_result(table, self.reset_time)
            
            if table == 'critical_results':
                log_listbox = self.critical_ng_log
            else:
                log_listbox = self.normal_ng_log 
            
            # 기존 로그 삭제
            log_listbox.delete(0, tk.END)
            
            # DB에서 읽어온 로그들을 UI에 표시
            for row in rows:
                # 불량이 있는 클라이언트들의 파트 정보 수집
                ng_parts = []  # 일반 불량 파트들
                none_parts = []  # 미검사 파트들
                critical_ng_parts = []  # 중대불량 파트들
                all_ok = True
                
                for client_id in line_config['client_ids']:
                    result_column = f"{client_id}_result"
                    if result_column in row and row[result_column]:
                        result_value = str(row[result_column]).upper()
                        if result_value == 'NONE':  # None인 경우 미검사로 처리
                            client_name = model_info['models'][MB.model_name][client_id]['name']
                            none_parts.append(client_name)
                            all_ok = False
                        elif ':' in result_value:  # 예)"5시 외관 검사:NG" 형태에서 파트 이름만 추출
                            part_name, label = result_value.split(':', 1)
                            if 'OK' not in label:
                                client_name = model_info['models'][MB.model_name][client_id]['name']
                                part_info = f"{client_name} {part_name}"
                                
                                # 중대불량 여부 확인
                                if table == 'critical_results' and label in model_info['models'][MB.model_name][client_id]['critical_ng_list']:
                                    critical_ng_parts.append(part_info)
                                else:
                                    ng_parts.append(part_info)
                                all_ok = False
                    else:
                        # 결과가 없는 경우도 미검사로 처리
                        client_name = model_info['models'][MB.model_name][client_id]['name']
                        none_parts.append(client_name)
                        all_ok = False
                
                # 전부 OK인 경우 로그를 남기지 않음
                if all_ok:
                    continue
                
                # 파트 정보 조합 (중대불량 우선)
                if table == 'critical_results' and critical_ng_parts:
                    # 중대불량이 있는 경우 중대불량을 우선 표시
                    all_parts = critical_ng_parts + ng_parts + none_parts
                    if len(all_parts) == 1:
                        part_info = all_parts[0]
                    else:
                        part_info = f"{all_parts[0]} 외 {len(all_parts)-1}"
                elif ng_parts and none_parts:  # 불량과 미검사가 혼재 - 하나로 통합
                    all_parts = ng_parts + none_parts
                    if len(all_parts) == 1:
                        part_info = all_parts[0]
                    else:
                        part_info = f"{all_parts[0]} 외 {len(all_parts)-1}"
                elif ng_parts:  # 불량만 있는 경우
                    if len(ng_parts) == 1:
                        part_info = ng_parts[0]
                    else:
                        part_info = f"{ng_parts[0]} 외 {len(ng_parts)-1}"
                elif none_parts:  # 미검사만 있는 경우
                    if len(none_parts) == 1:
                        part_info = f"{none_parts[0]} 미검사"
                    else:
                        part_info = f"{none_parts[0]} 외 {len(none_parts)-1}"

                # 불량 타입 정보 수집 (한글 이름으로 변환)
                ng_types = []
                for client_id in line_config['client_ids']:
                    result_column = f"{client_id}_result"
                    if result_column in row and row[result_column]:
                        result_value = str(row[result_column]).upper()
                        if result_value != 'NONE' and ':' in result_value:
                            part_name, label = result_value.split(':', 1)
                            if 'ERROR' in label:
                                ng_types.append('검사 오류')
                                break
                            elif label == 'DETECTION':
                                ng_types.append('각인 누락')
                                break
                            elif 'OK' not in label:
                                # label_ng_conditions에서 한글 이름 찾기
                                for client_id_check in line_config['client_ids']:
                                    if label in model_info['models'][MB.model_name][client_id_check]['label_ng_conditions']:
                                        korean_name = model_info['models'][MB.model_name][client_id_check]['label_ng_conditions'][label][0]
                                        ng_types.append(korean_name)
                                        break
                
                # 불량 타입 조합
                if not ng_types and none_parts:
                    ng_type = "미검사"
                elif len(ng_types) == 1:
                    ng_type = ng_types[0]
                else:
                    ng_type = f"{ng_types[0]} 외 {len(ng_types)-1}건"
                
                # 로그 형식: [시간] 파트 정보
                #           : 불량 타입
                log_time = row['input_time'].strftime('%H:%M:%S')
                
                # 첫 번째 줄 (시간 + 파트 정보)
                log_listbox.insert(tk.END, f"[{log_time}] {part_info}")
                # 두 번째 줄 (불량 타입)
                log_listbox.insert(tk.END, f"  : {ng_type}")

    def clear_ng_log_listboxes(self):
        """중대/일반 불량 이력 리스트 박스 로그 모두 초기화"""
        self.reset_time = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        model_info['reset_info']['time'] = self.reset_time
        self.save_info_json(model_info)
        SS.send_json()
        self.critical_ng_log.delete(0, tk.END)
        self.normal_ng_log.delete(0, tk.END)
        
    def on_log_select(self, event):
        """로그 선택 이벤트 핸들러 (중대/일반 불량 통합)"""
        # 카메라별 불량 수량 확인 모드 종료
        if self.ng_statistics_mode:
            self.toggle_ng_statistics_mode()
        
        # 어떤 리스트박스에서 이벤트가 발생했는지 확인
        widget = event.widget
        
        # 클릭한 위치가 실제 항목인지 확인
        index = widget.nearest(event.y)
        if index < 0:
            # 빈 공간을 클릭한 경우 선택 해제
            widget.selection_clear(0, tk.END)
            return
        
        self.ng_log_checking = True
        self.main_canvas.itemconfig(self.ng_log_checking_popup, state='normal')

        # 다른 리스트박스의 선택 해제
        if widget == self.critical_ng_log:
            self.normal_ng_log.selection_clear(0, tk.END)
        else:
            self.critical_ng_log.selection_clear(0, tk.END)
        
        if not widget.curselection():
            return
            
        selected_idx = widget.curselection()[0]
        pair_idx = selected_idx - (selected_idx % 2)  # 짝수 인덱스 (첫 번째 줄)
        
        # 선택된 항목들을 쌍으로 선택
        widget.selection_clear(0, tk.END)
        widget.selection_set(pair_idx)
        widget.selection_set(pair_idx + 1)
        
        # 로그에서 시간 추출
        log_line = widget.get(pair_idx)  # 첫 번째 줄 (시간 포함)
        import re
        match = re.search(r"\[(\d{2}:\d{2}:\d{2})\]", log_line)
        if not match:
            return
        
        log_time = match.group(1)  # '18:06:30'
        
        # 해당 테이블에서 로그 조회
        if widget == self.critical_ng_log:
            table_name = 'critical_results'
        else:
            table_name = 'normal_results'
        
        # DB에서 해당 시간의 로그 조회
        row = DB.get_result_by_time_from_table(log_time, table_name)
        if row:
            self.main_show_log_images_from_row(row)
        else:
            LM.log_print(f"[ERROR] No result found for time: {log_time} in {table_name}")

    def clear_log_images(self):
        """로그 이미지 초기화"""
        self.main_canvas.itemconfig(self.ng_log_checking_popup, state='hidden')
        self.ng_log_checking = False
        HW.display_results_images(HW.station4_dict)  # 마지막 결과 다시 표시

    def on_log_key(self, event):
        """로그 방향키 이동"""
        widget = event.widget
        size = widget.size()
        sel = widget.curselection()
        if not sel:
            return
        idx = sel[0] - (sel[0] % 2)
        if event.keysym == "Up":
            new_idx = max(0, idx - 2)
        elif event.keysym == "Down":
            new_idx = min(size - 2, idx + 2)
        else:
            return
        widget.selection_clear(0, tk.END)
        widget.selection_set(new_idx)
        widget.selection_set(new_idx + 1)
        widget.activate(new_idx)  # 커서를 첫 줄로 이동
        widget.see(new_idx)
        # 방향키 이동 시에도 on_log_select를 호출하여 이미지 등 갱신
        fake_event = type('Event', (object,), {'widget': widget, 'y': 0})()
        self.on_log_select(fake_event)

    def main_show_log_images_from_row(self, row):
        """DB 행 데이터에서 이미지 표시"""
        for client_id in line_config['client_ids']:
            result_column = f"{client_id}_result"
            path_column = f"{client_id}_path"
            
            # 결과와 이미지 경로 가져오기
            result_value = row.get(result_column, 'None')
            if ':' in result_value:
                label = str(result_value.split(':')[1]).upper()
            else:
                label = str(result_value).upper()
            image_path = row.get(path_column, 'None')
            
            # 표시 인덱스 가져오기
            display_idx = HW.inspection_sequence[client_id]
            
            # 이미지 생성 및 표시
            show_image = None
            
            # 결과가 None or error인 경우
            if label == 'NONE' or 'ERROR' in label:
                show_image = HW.make_show_image(client_id, label, None)
            else:  # 검사 결과 정상인 경우
                try:
                    abs_path = os.path.join('db', image_path)
                    image = cv2.imread(abs_path)
                    show_image = HW.make_show_image(client_id, label, image)
                except Exception as e:
                    LM.log_print(f"[ERROR] Failed to load image: {str(e)}")
                    show_image = HW.make_show_image(client_id, 'ERROR', None)
            
            # 캔버스에 이미지 표시
            self.show_image_list[display_idx] = show_image
            self.main_canvas.itemconfig(self.show_place_list[display_idx], 
                                       image=self.show_image_list[display_idx], 
                                       state='normal')
            
            # OK/NG 신호 표시
            self.switch_ok_ng_sign(label, display_idx)

    # -------------------- 클라이언트 연결 상태 관리 -------------------- #

    def connect_complete_check(self, client_id, connected):
        """클라이언트 연결 완료 확인"""
        try:
            idx = line_config['client_ids'].index(client_id)
            if connected:
                # 연결 성공 시에만 connecting 상태로 설정하고 깜빡임 시작
                self.client_connection_states[idx] = 'connecting'
                
                # 이미지를 정상 이미지로 설정 (이전 실패 이미지에서 복구)
                self.main_canvas.itemconfig(self.client_connect_complete_place_list[idx], 
                                           image=self.client_connect_complete_image, state='normal')
                
                self.start_client_blink(client_id, -1)  # 무한 깜빡임 (모델 로드 완료까지)
                
                # connecting 타임아웃 설정 (20초 후 failed로 변경)
                self._start_connecting_timeout(client_id)
                
                # 이전 실패 정보 초기화
                if client_id in self.client_load_failures:
                    del self.client_load_failures[client_id]
                
            else:
                # 연결 해제 시 disconnected 상태로 설정
                self.client_connection_states[idx] = 'disconnected'
                self.stop_client_blink(client_id)
                self._stop_connecting_timeout(client_id)
        except ValueError:
            LM.log_print(f"[ERROR] Invalid client_id: {client_id}")

    def _start_connecting_timeout(self, client_id):
        """connecting 상태 타임아웃 시작"""
        try:
            idx = line_config['client_ids'].index(client_id)
            
            # 기존 타임아웃 타이머가 있으면 취소
            if self.client_connecting_timers[idx]:
                self.master.after_cancel(self.client_connecting_timers[idx])
            
            # 새로운 타임아웃 타이머 설정
            self.client_connecting_timers[idx] = self.master.after(
                self.connecting_timeout, 
                lambda: self._handle_connecting_timeout(client_id)
            )
            
        except ValueError:
            LM.log_print(f"[ERROR] Invalid client_id for timeout: {client_id}")

    def _stop_connecting_timeout(self, client_id):
        """connecting 상태 타임아웃 중지"""
        try:
            idx = line_config['client_ids'].index(client_id)
            
            if self.client_connecting_timers[idx]:
                self.master.after_cancel(self.client_connecting_timers[idx])
                self.client_connecting_timers[idx] = None
                
        except ValueError:
            LM.log_print(f"[ERROR] Invalid client_id for stop timeout: {client_id}")

    def _handle_connecting_timeout(self, client_id):
        """connecting 상태 타임아웃 처리"""
        try:
            idx = line_config['client_ids'].index(client_id)
            
            # 현재 상태가 connecting인 경우에만 처리
            if self.client_connection_states[idx] == 'connecting':
                # 매뉴얼 모드가 수동일 때만 failed로 변경
                if MB.manual_mode:
                    LM.log_print(f"[TIMEOUT] {client_id} connecting timeout - setting to failed (manual mode)")
                    self.set_client_connection_failed(client_id)
                else:
                    # 자동 모드일 때는 계속 깜빡임 유지
                    LM.log_print(f"[TIMEOUT] {client_id} connecting timeout - keeping blink (auto mode)")
                    # 깜빡임은 계속 유지되므로 별도 처리 불필요
            
            # 타임아웃 타이머 초기화
            self.client_connecting_timers[idx] = None
            
        except ValueError:
            LM.log_print(f"[ERROR] Invalid client_id for timeout handling: {client_id}")

    def set_client_connection_failed(self, client_id):
        """클라이언트 연결 실패 상태 설정"""
        try:
            idx = line_config['client_ids'].index(client_id)

            # 깜빡임 중지
            self.stop_client_blink(client_id)
            
            # connecting 타임아웃 중지
            self._stop_connecting_timeout(client_id)
            
            # 실패 상태로 설정하고 실패 이미지 표시
            self.client_connection_states[idx] = 'failed'
            self.main_canvas.itemconfig(self.client_connect_complete_place_list[idx], 
                                        image=self.client_connect_fail_image, state='normal')
            LM.log_print(f"[FAILED] {client_id} connection failed (manual mode)")
            
        except ValueError:
            LM.log_print(f"[ERROR] Invalid client_id for failed state: {client_id}")

    def set_client_model_load_complete(self, client_id):
        """클라이언트 모델 로드 완료 상태 설정"""
        try:
            idx = line_config['client_ids'].index(client_id)
            
            # 깜빡임 중지
            self.stop_client_blink(client_id)
            
            # connecting 타임아웃 중지
            self._stop_connecting_timeout(client_id)
            
            # 연결 완료 상태로 설정하고 정상 이미지 표시
            self.client_connection_states[idx] = 'connected'
            self.main_canvas.itemconfig(self.client_connect_complete_place_list[idx], 
                                       image=self.client_connect_complete_image, state='normal')
            
        except ValueError:
            LM.log_print(f"[ERROR] Invalid client_id for complete state: {client_id}")

    def start_client_blink(self, client_id, duration=3000):
        """클라이언트 연결 상태 이미지 깜빡임 시작
        Args:
            client_id: 클라이언트 ID
            duration: 깜빡임 지속 시간 (밀리초, -1이면 무한 깜빡임)
        """
        try:
            idx = line_config['client_ids'].index(client_id)
            
            # 기존 타이머가 있으면 취소
            if self.client_blink_timers[idx]:
                self.master.after_cancel(self.client_blink_timers[idx])
            
            # 깜빡임 상태 초기화
            self.client_blink_states[idx] = False
            
            # 깜빡임 시작
            self._blink_client_icon(idx, duration)
            
        except ValueError:
            LM.log_print(f"[ERROR] Invalid client_id for blink: {client_id}")

    def stop_client_blink(self, client_id):
        """클라이언트 연결 상태 이미지 깜빡임 중지
        Args:
            client_id: 클라이언트 ID
        """
        try:
            idx = line_config['client_ids'].index(client_id)
            
            # 타이머 취소
            if self.client_blink_timers[idx]:
                self.master.after_cancel(self.client_blink_timers[idx])
                self.client_blink_timers[idx] = None
            
            # 연결 상태에 따라 이미지 설정
            if self.client_connection_states[idx] == 'disconnected':
                # 연결 해제 상태면 숨김
                self.client_blink_states[idx] = False
                self.main_canvas.itemconfig(self.client_connect_complete_place_list[idx], state='hidden')
            # connecting, failed, connected 상태는 각각의 함수에서 처리
            
        except ValueError:
            LM.log_print(f"[ERROR] Invalid client_id for stop blink: {client_id}")

    def _blink_client_icon(self, idx, duration):
        """클라이언트 아이콘 깜빡임 내부 함수
        Args:
            idx: 클라이언트 인덱스
            duration: 남은 깜빡임 시간 (밀리초, -1이면 무한)
        """
        if duration == 0:
            # 깜빡임 종료
            self.client_blink_timers[idx] = None
            if self.client_connection_states[idx] == 'disconnected':
                self.main_canvas.itemconfig(self.client_connect_complete_place_list[idx], state='hidden')
            return
        
        # 깜빡임 상태 토글
        self.client_blink_states[idx] = not self.client_blink_states[idx]
        
        # 이미지 표시/숨김
        state = 'normal' if self.client_blink_states[idx] else 'hidden'
        self.main_canvas.itemconfig(self.client_connect_complete_place_list[idx], state=state)
        
        # 다음 깜빡임 예약 (500ms 간격)
        next_duration = duration - 500 if duration > 0 else -1
        self.client_blink_timers[idx] = self.master.after(500, lambda: self._blink_client_icon(idx, next_duration))

    def stop_all_client_blinks(self):
        """모든 클라이언트 깜빡임 중지"""
        for client_id in line_config['client_ids']:
            self.stop_client_blink(client_id)

    def is_client_status_click(self, x, y):
        """클라이언트 상태 영역 클릭 여부 확인"""
        # 클라이언트 상태 표시 영역 좌표들
        client_areas = []
        for i in range(client_num):
            if i < 3:
                # 상단 3개 클라이언트
                client_areas.append((1071 + (i * 128), 31, 1071 + (i * 128) + 128, 31 + 42))
            else:
                # 하단 3개 클라이언트
                client_areas.append((1071 + ((i - 3) * 128), 73, 1071 + ((i - 3) * 128) + 128, 73 + 42))
        
        # 클릭 위치가 어느 영역에 속하는지 확인
        for area in client_areas:
            if area[0] <= x <= area[2] and area[1] <= y <= area[3]:
                return True
        return False

    def get_client_index_from_click(self, x, y):
        """클릭 위치에서 클라이언트 인덱스 반환"""
        for i in range(client_num):
            if i < 3:
                # 상단 3개 클라이언트
                if 1071 + (i * 128) <= x <= 1071 + (i * 128) + 128 and 31 <= y <= 31 + 42:
                    return i
            else:
                # 하단 3개 클라이언트
                if 1071 + ((i - 3) * 128) <= x <= 1071 + ((i - 3) * 128) + 128 and 73 <= y <= 73 + 42:
                    return i
        return None

    def show_client_status_popup(self, client_idx):
        """클라이언트 상태 팝업 표시"""
        # 기존 팝업이 있으면 닫기
        if self.client_status_popup:
            try:
                self.client_status_popup.destroy()
            except:
                pass
            self.client_status_popup = None
        
        # 클라이언트 ID 가져오기
        if client_idx < len(line_config['client_ids']):
            client_id = line_config['client_ids'][client_idx]
        else:
            return
        
        # 현재 상태 가져오기
        current_state = self.client_connection_states[client_idx]
        
        # 팝업 생성
        self.client_status_popup = tk.Toplevel(self)
        self.client_status_popup.title(f"클라이언트 상태 - {client_id}")
        self.client_status_popup.geometry("500x500")
        self.client_status_popup.configure(bg='#2a5565')
        
        # 팝업이 닫힐 때 변수 초기화
        def on_popup_close():
            popup_to_destroy = self.client_status_popup
            self.client_status_popup = None
            popup_to_destroy.destroy()
        
        self.client_status_popup.protocol("WM_DELETE_WINDOW", on_popup_close)
        
        # 메인 프레임
        main_frame = tk.Frame(self.client_status_popup, bg='#2a5565')
        main_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=20)
        
        # 제목
        title_text = f"클라이언트: {client_id}"
        if current_state == 'failed' and client_id in self.client_load_failures:
            load_type = self.client_load_failures[client_id]
            title_text += f" - {self.get_load_failure_title(load_type)}"
        
        title_label = tk.Label(main_frame, text=title_text, 
                              font=('Malgun Gothic', 16, 'bold'), bg='#2a5565', fg='white')
        title_label.pack(pady=(0, 20))
        
        # 상태 정보
        status_frame = tk.Frame(main_frame, bg='#2a5565')
        status_frame.pack(fill=tk.BOTH, expand=True)
        
        # 현재 상태
        state_text = self.get_state_description(current_state)
        state_color = self.get_state_color(current_state)
        
        state_label = tk.Label(status_frame, text=f"현재 상태: {state_text}", 
                              font=('Malgun Gothic', 14, 'bold'), bg='#2a5565', fg=state_color)
        state_label.pack(pady=10)
        
        # 상태별 상세 정보
        detail_text = self.get_state_detail(client_id, current_state)
        detail_label = tk.Label(status_frame, text=detail_text, 
                               font=('Malgun Gothic', 12), bg='#2a5565', fg='white', 
                               wraplength=350, justify=tk.LEFT)
        detail_label.pack(pady=10)
        
        # 연결 정보
        if client_id in SS.client_info:
            connection_info = f"IP 주소: {SS.client_info[client_id]['addr'][0]}\n포트: {SS.client_info[client_id]['addr'][1]}"
        else:
            connection_info = "연결 정보 없음"
        
        info_label = tk.Label(status_frame, text=connection_info, 
                             font=('Malgun Gothic', 11), bg='#2a5565', fg='#cccccc')
        info_label.pack(pady=10)
        
        # 닫기 버튼
        close_button = tk.Button(main_frame, text="닫기", command=on_popup_close,
                                font=('Malgun Gothic', 12, 'bold'), bg='#666666', fg='white')
        close_button.pack(pady=20)

    def get_state_description(self, state):
        """상태에 대한 설명 반환"""
        state_descriptions = {
            'disconnected': '연결 해제',
            'connecting': '연결 중',
            'failed': '검사 준비 실패',
            'connected': '연결 완료'
        }
        return state_descriptions.get(state, '알 수 없음')

    def get_state_color(self, state):
        """상태에 대한 색상 반환"""
        state_colors = {
            'disconnected': '#cccccc',
            'connecting': '#ffff00',  # 노란색
            'failed': '#ff4444',      # 빨간색
            'connected': '#44ff44'    # 초록색
        }
        return state_colors.get(state, '#ffffff')

    def get_state_detail(self, client_id, state):
        """상태별 상세 정보 반환"""
        if state == 'disconnected':
            return "클라이언트가 연결되지 않았습니다.\n클라이언트 프로그램을 실행하고 연결을 시도해주세요."
        
        elif state == 'connecting':
            return "클라이언트가 연결되어 모델을 로드하고 있습니다.\n잠시 기다려주세요."
        
        elif state == 'failed':
            # 구체적인 로드 실패 정보 확인
            if client_id in self.client_load_failures:
                load_type = self.client_load_failures[client_id]
                return self.get_load_failure_detail(load_type)
            else:
                return "검사 준비를 실패했습니다.\n가능한 원인:\n• 모델 로드 실패\n• 네트워크 연결 문제\n• 클라이언트 프로그램 오류\n\n클라이언트를 재시작하고 다시 연결을 시도해주세요."
        
        elif state == 'connected':
            return "클라이언트가 정상적으로 연결되어 있습니다.\n모델 로드가 완료되어 검사 준비가 되었습니다."
        
        else:
            return "알 수 없는 상태입니다."

    def get_load_failure_detail(self, load_type):
        """로드 실패 타입별 상세 정보 반환"""
        failure_details = {
            'classi_masking': "원인:\n• 마스킹 이미지 파일이 존재하지 않음\n• 마스킹 이미지 파일 형식 오류\n• 마스킹 이미지 파일 경로 오류\n\n해결 방법:\n• 마스킹 이미지 파일 확인\n• 파일 경로 및 형식 확인\n• 클라이언트 재시작",
            
            'classi_model': "원인:\n• 모델 파일이 존재하지 않음\n• 모델 파일 형식 오류\n• 모델 파일 경로 오류\n\n해결 방법:\n• 모델 파일 용량 확인\n• 모델 파일 경로 확인\n• 클라이언트 재시작",
            
            'det_masking': "원인:\n• 마스킹 이미지 파일이 존재하지 않음\n• 마스킹 이미지 파일 형식 오류\n• 마스킹 이미지 파일 경로 오류\n\n해결 방법:\n• 마스킹 이미지 파일 확인\n• 파일 경로 및 형식 확인\n• 클라이언트 재시작",
            
            'det_model': "원인:\n• 모델 파일이 존재하지 않음\n• 모델 파일 형식 오류\n• 모델 파일 경로 오류\n\n해결 방법:\n• 모델 파일 용량 확인\n• 모델 파일 경로 확인\n• 클라이언트 재시작"
        }
        
        return failure_details.get(load_type, f"알 수 없는 로드 실패: {load_type}\n\n클라이언트를 재시작하고 다시 시도해주세요.")

    def get_load_failure_title(self, load_type):
        """로드 실패 타입별 제목 반환"""
        failure_titles = {
            'classi_masking': '분류 마스킹 로드 실패',
            'classi_model': '분류 모델 로드 실패',
            'det_masking': '디텍션 마스킹 로드 실패',
            'det_model': '디텍션 모델 로드 실패'
        }
        
        return failure_titles.get(load_type, f'알 수 없는 실패: {load_type}')
    
    # -------------------- 카메라별 불량 수량 확인 -------------------- #

    def toggle_ng_statistics_mode(self):
        """불량 수량 확인 모드 토글"""
        if self.ng_statistics_mode:
            self.exit_ng_statistics_mode()
        else:
            self.enter_ng_statistics_mode()

    def enter_ng_statistics_mode(self):
        """불량 수량 확인 모드 시작"""
        self.ng_statistics_mode = True
        self.main_canvas.itemconfig(self.main_frame_btn_place, state='normal')
        self.main_canvas.itemconfig(self.camera_ng_count_check_btn_place, state='normal')
        
        # 기존 검사 이미지들 숨기기
        for i in range(client_num):
            self.main_canvas.itemconfig(self.show_place_list[i], state='hidden')
            self.main_canvas.itemconfig(self.ok_sign_place_list[i], state='hidden')
            self.main_canvas.itemconfig(self.ng_sign_place_list[i], state='hidden')
        
        # 불량 수량 생성 및 표시
        self.show_ng_statistics()

    def exit_ng_statistics_mode(self):
        """불량 수량 확인 모드 종료"""
        self.ng_statistics_mode = False
        self.main_canvas.itemconfig(self.main_frame_btn_place, state='hidden')
        self.main_canvas.itemconfig(self.camera_ng_count_check_btn_place, state='hidden')

        # 불량 수량 확인 리스트박스들 완전 제거
        if hasattr(self, 'statistics_listboxes'):
            for listbox in self.statistics_listboxes:
                try:
                    listbox.destroy()
                except:
                    pass
            self.statistics_listboxes = []
        
        # 불량 수량 확인 프레임들 완전 제거
        if hasattr(self, 'statistics_frames'):
            for frame in self.statistics_frames:
                try:
                    frame.destroy()
                except:
                    pass
            self.statistics_frames = []
        
        # 원래 이미지로 복원
        HW.display_results_images(HW.station4_dict)  # 마지막 결과 다시 표시

    def show_ng_statistics(self):
        """불량 수량 리스트박스로 표시"""
        try:
            # 기존 불량 수량 리스트박스들 제거
            if hasattr(self, 'statistics_listboxes'):
                for listbox in self.statistics_listboxes:
                    try:
                        # 리스트박스의 부모 프레임까지 모두 제거
                        parent = listbox.master
                        if parent:
                            parent.destroy()
                    except:
                        pass
            
            self.statistics_listboxes = []
            self.statistics_frames = []
            
            # 각 클라이언트별로 개별 불량 수량 생성 및 표시
            for i, client_id in enumerate(line_config['client_ids']):
                # 해당 클라이언트의 불량 수량 데이터 가져오기
                client_statistics = self.get_client_ng_statistics_data(client_id)
                
                # 리스트박스 생성
                listbox, frame = self.create_statistics_listbox(client_statistics, client_id, i)
                self.statistics_listboxes.append(listbox)
                self.statistics_frames.append(frame)
                
        except Exception as e:
            LM.log_print(f"[ERROR] Failed to show NG statistics: {str(e)}")
            import traceback
            traceback.print_exc()

    def create_statistics_listbox(self, statistics_data, client_id, position):
        """특정 클라이언트의 불량 수량 표시할 리스트박스 생성"""
        try:
            # 클라이언트 이름
            client_name = model_info['models'][MB.model_name][client_id]['name']
            
            # 리스트박스 프레임 생성 (크기 고정)
            frame = tk.Frame(self.main_canvas, bg='#2a5565', relief=tk.RAISED, bd=2, width=391, height=290)
            frame.pack_propagate(False)  # 프레임 크기 고정
            
            # 프레임 위치 계산 (기존 이미지 위치와 동일)
            if position < 3:
                x_pos = 96 + (position * 441)
                y_pos = 140
            else:
                x_pos = 96 + ((position - 3) * 441)
                y_pos = 553
            
            # 프레임을 캔버스에 배치
            self.main_canvas.create_window(x_pos, y_pos, window=frame, anchor="nw")
            
            # 제목 라벨
            title_label = tk.Label(frame, text=f"{client_name}", 
                                  font=('Malgun Gothic', 14, 'bold'), 
                                  bg='#2a5565', fg='white')
            title_label.pack(pady=(5, 0))
            
            # 리스트박스와 스크롤바를 담을 프레임
            list_frame = tk.Frame(frame, bg='#2a5565')
            list_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
            
            # 리스트박스 생성 (크기 조정)
            listbox = tk.Listbox(list_frame, font=('Malgun Gothic', 10), 
                                bg='#2a5565', fg='white', 
                                selectmode='none', 
                                height=12, width=45,
                                relief=tk.FLAT, bd=0)
            listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
            
            # 스크롤바 추가
            scrollbar = tk.Scrollbar(list_frame, orient="vertical", command=listbox.yview)
            scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
            listbox.config(yscrollcommand=scrollbar.set)
            
            # 불량 수량 데이터 추가
            listbox.insert(tk.END, f"총 불량: {statistics_data['total_ng']}개")
            listbox.insert(tk.END, f"중대불량: {statistics_data['critical_ng']}개")
            listbox.insert(tk.END, f"일반불량: {statistics_data['normal_ng']}개")
            
            # 구분선 추가
            if statistics_data['label_ng']:
                listbox.insert(tk.END, "")
                listbox.insert(tk.END, "─" * 35)  # 구분선 길이 조정
                listbox.insert(tk.END, "")
                
                # 라벨별 불량 수량 추가 (개수 순으로 정렬)
                for label, count in sorted(statistics_data['label_ng'].items(), key=lambda x: x[1], reverse=True):
                    if count > 0:
                        # 라벨의 한글 이름 찾기
                        korean_name = label
                        if client_id in model_info['models'][MB.model_name]:
                            if label in model_info['models'][MB.model_name][client_id]['label_ng_conditions']:
                                korean_name = model_info['models'][MB.model_name][client_id]['label_ng_conditions'][label][0]
                        
                        listbox.insert(tk.END, f"{korean_name}: {count}개")
            
            return listbox, frame
            
        except Exception as e:
            LM.log_print(f"[ERROR] Failed to create statistics listbox for {client_id}: {str(e)}")
            import traceback
            traceback.print_exc()
            return None, None

    def get_client_ng_statistics_data(self, client_id):
        """특정 클라이언트의 불량 수량 데이터 가져오기"""
        statistics = {
            'total_ng': 0,
            'critical_ng': 0,
            'normal_ng': 0,
            'label_ng': {}
        }
        
        try:
            # 전체 불량 개수 (reset_time 이후)
            critical_results = DB.read_result('critical_results', self.reset_time, limit=99999)
            normal_results = DB.read_result('normal_results', self.reset_time, limit=99999)
            
            # 해당 클라이언트의 라벨별 불량 개수 초기화
            if client_id in model_info['models'][MB.model_name]:
                for label in model_info['models'][MB.model_name][client_id]['label_ng_conditions']:
                    statistics['label_ng'][label] = 0
            
            # 미검사&오류 카운트 추가
            statistics['label_ng']['미검사'] = 0
            statistics['label_ng']['오류'] = 0
            
            # 결과 데이터에서 해당 클라이언트의 불량 개수 계산
            for table_name, results in [('critical_results', critical_results), ('normal_results', normal_results)]:
                for row in results:
                    result_column = f"{client_id}_result"
                    if result_column in row and row[result_column]:
                        result_value = str(row[result_column]).upper()
                        if result_value == 'NONE':
                            statistics['label_ng']['미검사'] += 1
                            statistics['normal_ng'] += 1
                            statistics['total_ng'] += 1
                        elif 'ERROR' in result_value:
                            statistics['label_ng']['오류'] += 1
                            statistics['normal_ng'] += 1
                            statistics['total_ng'] += 1
                        elif ':' in result_value:
                            part_name, label = result_value.split(':', 1)
                            if 'OK' not in label:
                                # 전체 카운트
                                if table_name == 'critical_results':
                                    statistics['critical_ng'] += 1
                                else:
                                    statistics['normal_ng'] += 1
                                statistics['total_ng'] += 1
                                
                                # 라벨별 카운트
                                if label in statistics['label_ng']:
                                    statistics['label_ng'][label] += 1
            
        except Exception as e:
            LM.log_print(f"[ERROR] Failed to get client NG statistics data for {client_id}: {str(e)}")
        
        return statistics


# ▶ 메인 - 클라이언트 소켓 서버 클래스 
class SocketServer:
    def __init__(self, host, port):
        self.host = host
        self.port = port
        self.client_info = {}
        self.connect_complete = False
        self.db_saveQ = MQueue()  # DB저장용 큐
        
        self.message_queue = MQueue()  # 메시지 전송용 큐
        self.message_thread = None  # 메시지 전송 스레드
        
        # 라인 설정 로드
        self.client_map = line_config['ip_map']  # 클라이언트 IP 맵핑
        self.load_complete_check_dict = create_bool_dict(line_config['client_ids'], False)  # 로드 완료 확인용 딕셔너리
        self.result_dict = create_result_dict(line_config['client_ids'])  # 검사 결과 딕셔너리
        self.gpu_avail_dict = create_bool_dict(line_config['client_ids'], True)  # GPU 사용 가능 여부 딕셔너리
        
        self.create_server()

    def create_server(self) : 
        """소켓 서버 생성"""
        while True :
            try :
                self.server_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                self.server_socket.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
                self.server_socket.bind((self.host, self.port))
                self.server_socket.listen(5)
                self.client_connecting_start_time = time.time()
                LM.log_print(f"[SOCKET] Main-Client Connecting Start: {self.host}:{self.port}")
                break
            except:
                LM.log_print(f"[SOCKET] Main-Client Connecting Failed: {traceback.format_exc()}")
                time.sleep(1)

    def message_sender(self):
        """메시지 전송 스레드 - 큐에서 메시지를 순차적으로 전송"""
        while True:
            try:
                try:
                    message_data = self.message_queue.get(timeout=1)
                except:
                    continue  # 타임아웃 시 다시 대기
                
                client_id = message_data['client_id']
                msg = message_data['message']
                
                # 실제 메시지 전송
                self._send_message_internal(client_id, msg)
                
            except Exception as e:
                LM.log_print(f"[SOCKET] Message sender error: {str(e)}")
                time.sleep(0.1)

    def _send_message_internal(self, client_id, msg):
        """내부 메시지 전송 함수 (스레드 안전)"""
        try:
            msg_encoded = msg.encode('utf-8') 
            msg_length = len(msg_encoded)
            length_info = msg_length.to_bytes(4, byteorder='big')

            if client_id == 'all':
                for client_id, client_info in self.client_info.items():
                    try:
                        client_socket = client_info['socket']
                        client_socket.send(length_info)
                        client_socket.send(msg_encoded)
                    except Exception as e:
                        LM.log_print(f'[SOCKET] Failed to send to {client_id}: {str(e)}')
            else:
                if client_id in self.client_info:
                    client_socket = self.client_info[client_id]['socket']
                    client_socket.send(length_info)
                    client_socket.send(msg_encoded)
                else:
                    LM.log_print(f'[SOCKET] Client {client_id} not found in client_info')
                    
        except Exception as e:
            LM.log_print(f'[SOCKET] Message send failed for {client_id}: {str(e)}')

    def connect_thread(self):
        """클라이언트 소켓 연결 스레드"""
        while True:
            try:
                if not self.connect_complete:
                    LM.log_print("[SOCKET] Main-Client Connecting Start")
                    client_socket, addr = self.server_socket.accept()
                    client_ip = addr[0]
                    client_id = self.client_map[client_ip]
                    self.client_info[client_id] = {"socket": client_socket, "addr": addr}
                    threading.Thread(target=self.recv_from_client, args=(client_socket, client_id), daemon=True).start()
                    LM.log_print(f"[SOCKET] Main-Client Connecting Complete: {client_id}-{client_ip}")
                    MF.connect_complete_check(client_id, True)
                    
                    if len(self.client_info) == 1:  # 테스트용 > client_num 으로 변경
                        self.connect_complete = True
                        if MB.model_name:  # 모든 클라이언트 연결완료되었는데 모델 번호가 존재할 때 = 재연결
                            LM.log_print(f"[SOCKET] Sending model load signals to reconnected clients")
                            self.send_json_and_model(client_id)
                else:
                    time.sleep(1)
            except:
                LM.log_print(f'[SOCKET] Main-Client Connecting Failed: {traceback.format_exc()}')
                time.sleep(1)

    def send_json(self, client_id=None):
        """클라이언트로 JSON 파일 전송"""
        # 전송할 클라이언트 목록 결정
        target_clients = line_config['client_ids'] if client_id is None else [client_id]
        
        for target_id in target_clients:
            msg = model_info['models'][MB.model_name][target_id]
            json_string = f'json:{json.dumps(msg, ensure_ascii=False)}'

            # 큐에 메시지 추가
            self.message_queue.put({
                'client_id': target_id,
                'message': json_string
            })
            LM.log_print(f"[SOCKET] JSON queued for {target_id}")
    
    def send_json_and_model(self, client_id=None):
        """모델 로드 신호 전송 : Json과 model 동시 전송"""
        # 전송할 클라이언트 목록 결정
        target_clients = line_config['client_ids'] if client_id is None else [client_id]
        
        for target_id in target_clients:
            json_data = model_info['models'][MB.model_name][target_id]
            json_string = json.dumps(json_data, ensure_ascii=False)
            msg = f'model:{MB.model_name}:{json_string}'

            # 큐에 메시지 추가
            self.message_queue.put({
                'client_id': target_id,
                'message': msg
            })
            LM.log_print(f"[SOCKET] JSON queued for {target_id}")

    def send_msg_to_client(self, msg, client_id=None):
        """클라이언트에게 메시지 전송 (큐를 통해)"""
        # 전송할 클라이언트 목록 결정
        target_clients = line_config['client_ids'] if client_id is None else [client_id]

        for target_id in target_clients:
            self.message_queue.put({
                'client_id': target_id,
                'message': msg
            })
            LM.log_print(f"[SOCKET] Message queued for {target_id}: {msg[:10]}...")

    def recvall(self, sock, count):
        """데이터 수신"""
        buf = b""
        while count:
            newbuf = sock.recv(count)
            if not newbuf:
                return None
            buf += newbuf
            count -= len(newbuf)
        return buf
    
    def recv_from_client(self, client_socket, client_id):
        """클라이언트 프로그램으로부터 데이터 수신"""
        while True:
            try:
                time.sleep(0.005)
                header = self.recvall(client_socket, 4)
                if not header:
                    LM.log_print(f"[SOCKET] {client_id} Header Not Received")
                    break

                data_length = int.from_bytes(header, 'big')  # 데이터 길이 추출
                data = self.recvall(client_socket, data_length)  # 실제 데이터 수신

                if data:
                    recvData = data.decode().strip()
                    print(f"[SOCKET] {client_id} Response: {recvData}")
                else:
                    LM.log_print(f"[SOCKET] {client_id} Connection Lost")
                    break
                    
                if recvData == 'model_load_complete':  # 모델 로드 완료 수신
                    LM.log_print(f"[SOCKET] {client_id} Model Load Complete")
                    MF.set_client_model_load_complete(client_id)  # 연결 완료 상태로 설정
                    self.load_complete_check_dict[client_id] = True
                    if all(self.load_complete_check_dict.values()):
                        MB.modbus_queue.put({"mode": "ready"})
                        LM.log_print(f"[SOCKET] All Client Model Load Complete")
                
                elif 'update_labels' in recvData:  # 라벨 업데이트 수신
                    add_labels = recvData.split('|')[1]
                    remove_labels = recvData.split('|')[2]
                    LM.log_print(f"[UPDATE] {client_id}: add labels: {add_labels} | remove labels: {remove_labels}")
                    HW.update_labels(client_id, add_labels, remove_labels)
                    self.send_json(client_id)
                
                elif 'load' in recvData:
                    load_type = recvData.split(':')[1]
                    result = recvData.split(':')[2]
                    if result == 'fail':
                        LM.log_print(f"[ERROR] {client_id} {load_type} Failed")
                        MF.client_load_failures[client_id] = load_type
                        self.load_complete_check_dict[client_id] = False
                        MF.set_client_connection_failed(client_id)  # 연결 실패 상태로 설정
                    else:
                        # 로드 성공 시 실패 정보 제거
                        if client_id in MF.client_load_failures:
                            del MF.client_load_failures[client_id]
                
                elif 'result' in recvData:  # 검사 결과 수신
                    result_part = recvData.split(':')[1]
                    result_label = recvData.split(':')[2]
                    cycle_time = time.time() - MB.inspection_start_time
                    LM.log_print(f"[RESULT] {client_id}: {result_part} - {result_label} Received (Cycle Time: {cycle_time:.2f}s)")
                    self.result_dict[client_id]['part'] = result_part
                    self.result_dict[client_id]['label'] = result_label

                    length_bytes = self.recvall(client_socket, 4)
                    if length_bytes:
                        data_length = int.from_bytes(length_bytes, 'big')
                        binData = self.recvall(client_socket, data_length)
                        if binData:
                            try:
                                recv_image = pickle.loads(binData)
                                self.result_dict[client_id]['image'] = recv_image
                            except:
                                LM.log_print(f"[ERROR] {client_id} image unpickling error : {traceback.format_exc()}")
                                return
                    
                    HW.analysis_result()  # 검사 결과 종합 시도

                elif 'recent' in recvData:  # 최근 검사 결과 수신 ex) recent:ng:part_name:label
                    recent_type = recvData.split(':')[1]  # ng, ok, origin
                    recent_part = recvData.split(':')[2]  # 라벨명, engrave(각인)
                    recent_label = recvData.split(':')[3]

                    length_bytes = self.recvall(client_socket, 4)
                    if length_bytes:
                        data_length = int.from_bytes(length_bytes, 'big')
                        binData = self.recvall(client_socket, data_length)
                        if binData:
                            try:
                                recv_image = pickle.loads(binData)
                            except:
                                LM.log_print(f"[ERROR] {client_id} image unpickling error : {traceback.format_exc()}")
                                return
                            if recent_type == 'origin':  # 원본 이미지
                                is_origin_image = self.check_origin_image(client_id)
                                if is_origin_image:  # 원본 이미지 존재 시 원본 이미지 전송 중지
                                    SS.message_queue.put({
                                        'client_id': client_id,
                                        'message': f'recent:origin:stop'
                                    })
                                else:  # 원본 이미지 없으면 원본 이미지 전송 시작
                                    SS.message_queue.put({
                                        'client_id': client_id,
                                        'message': f'recent:origin:start'
                                    })
                                    self.save_recent_image_and_remove_oldest(client_id, recent_type, recent_part, recent_label, recv_image)
                            else:  # 각인 불량, 불량 이미지 저장
                                self.save_recent_image_and_remove_oldest(client_id, recent_type, recent_part, recent_label, recv_image)
                            
            
                elif 'gpu_available' in recvData:
                    gpu_available = recvData.split(':')[1]
                    if gpu_available == 'True':
                        self.gpu_avail_dict[client_id] = True
                    else:
                        self.gpu_avail_dict[client_id] = False
                    
            except:
                LM.log_print(f"[SOCKET] {client_id} Communication Error: {traceback.format_exc()}")
                break
            
        # 연결 제거
        if client_id in self.client_info:
            del self.client_info[client_id]
        client_socket.close()
        LM.log_print(f"[SOCKET] {client_id} Connection Closed")
        MF.connect_complete_check(client_id, False)
        self.connect_complete = False
        self.load_complete_check_dict[client_id] = False

    def save_recent_image_and_remove_oldest(self, client_id, recent_type, recent_part, recent_label, recv_image):
        """최근 검사 이미지 저장 및 가장 오래된 이미지 제거"""
        if recent_type == 'origin':
            save_path = os.path.join('recent_images', MB.model_name, client_id, recent_type)
        else:
            save_path = os.path.join('recent_images', MB.model_name, client_id, recent_part, recent_type)

        if recent_type == 'origin':
            img_name = f"{recent_type}.jpg"
        else:
            timestamp = datetime.datetime.now().strftime('%Y%m%d%H%M%S%f')
            if recent_part == 'engrave':
                img_name = f"engrave-{timestamp}.jpg"
            else:
                img_name = f"{recent_label}-{timestamp}.jpg"
        
        if recv_image is None:
            print(f"[ERROR] recv_image is None")
            return
        
        # 이미지 데이터 유효성 검사
        if hasattr(recv_image, 'shape'):
            if len(recv_image.shape) != 3 or recv_image.shape[2] != 3:
                print(f"[ERROR] Invalid image shape: {recv_image.shape}")
                return
            if recv_image.min() < 0 or recv_image.max() > 255:
                print(f"[ERROR] Invalid image values: min={recv_image.min()}, max={recv_image.max()}")
                return

        if not os.path.exists(save_path):
            try:
                os.makedirs(save_path)
            except Exception as e:
                print(f"[ERROR] Failed to create directory {save_path}: {e}")
                return

        all_files = [os.path.join(save_path, f) for f in os.listdir(save_path) if os.path.isfile(os.path.join(save_path, f))]
        
        if len(all_files) > 200:
            all_files.sort(key=os.path.getctime)
            try:
                os.remove(all_files[0])
                print(f"Removed oldest file: {all_files[0]}")
            except Exception as e:
                print(f"[ERROR] Failed to remove oldest file: {e}")
        
        # 이미지 저장 (PIL 사용 - 한글 경로 지원)
        full_path = os.path.join(save_path, img_name)

        try:
            rgb_image = cv2.cvtColor(recv_image, cv2.COLOR_BGR2RGB)
            pil_image = Image.fromarray(rgb_image)
            pil_image.save(full_path, 'JPEG', quality=95)
        except Exception as e:
            print(f"[ERROR] PIL save failed: {e}")

    def check_origin_image(self, client_id):
        """원본 이미지 존재 여부 확인"""
        save_path = f'recent_images/{MB.model_name}/{client_id}/origin'
        if os.path.exists(save_path):
            for file in os.listdir(save_path):
                if file.lower().endswith('.jpg'):
                    return True
        return False

# ▶ PLC(모드 버스) 통신 클래스
class Modbus:
    def __init__(self):
        self.modbus_device = None
        self.is_connected = False
        self.first_trigger = False
        
        # PLC 설정
        self.host = "192.168.50.55"  # PLC IP 주소 "192.168.0.2"
        self.port = 9999              # Modbus TCP 포트 "502"
        self.timeout = 5             # 연결 타임아웃
        
        # Modbus 주소 설정
        self.default_recv_address = 0  # 기본 수신 주소
        self.recv_modbus_signal = [0] * 10  # 수신 신호
        self.changed_modbus_signal = [False] * 10  # 변경 신호
        
        self.modbus_queue = MQueue()  # Modbus 명령 큐

        self.model_number = None  # 모델 번호
        self.model_name = None  # 모델 이름
        self.manual_mode = False  # 라인 모드 수동 여부
        self.result_request = False  # 검사 결과 요청 신호
        self.inspection_start_time = 0  # 검사 시작 시간
        
        self.connect_modbus()

    def connect_modbus(self):
        """모드버스 연결"""
        while True:
            try:
                # 기존 연결 정리
                if self.modbus_device:
                    try:
                        self.modbus_device.close()
                    except:
                        pass
                
                # 새 연결 생성
                self.modbus_device = ModbusTcpClient(
                    host=self.host, 
                    port=self.port, 
                    timeout=self.timeout
                )
                
                # 실제 연결 시도
                if not self.modbus_device.connect():
                    raise Exception(f"Modbus connection failed: {self.host}:{self.port}")
            
                # 초기 신호 전송
                if not self.first_trigger:
                    self.modbus_queue.put({"mode": "reset"})
                    self.first_trigger = True
                
                self.modbus_queue.put({"mode": "reconnect"})
                self.modbus_queue.put({"mode": "alive", "value": 1})
                
                self.is_connected = True
                LM.log_print(f"[PLC] Connected to {self.host}:{self.port}")
                return
                
            except Exception as e:
                self.is_connected = False
                LM.log_print(f"[PLC] Connection failed: {e}")
                time.sleep(1)

    def read_signal_thread(self):
        """PLC 신호 읽기 스레드"""
        cycle_check_count = 0
        while True:
            try:
                time.sleep(0.1)
                
                # 연결 상태 확인
                if not self.modbus_device or not self.is_connected:
                    time.sleep(0.1)
                    continue
                
                # PLC 데이터 읽기
                try:
                    values = self.modbus_device.read_holding_registers(self.default_recv_address, count=10)
                    value_list = values.registers
                except:
                    LM.log_print(f"[PLC] Read error: {traceback.format_exc()}")
                    self.is_connected = False
                    self.connect_modbus()
                    continue
                
                # 데이터 변경 감지
                for i in range(len(self.recv_modbus_signal)):
                    if self.recv_modbus_signal[i] != value_list[i]:
                        self.recv_modbus_signal[i] = value_list[i]
                        self.changed_modbus_signal[i] = True
                
                # PC Alive 1초 마다 전송(time.sleep(0.1))
                cycle_check_count += 1
                if cycle_check_count >= 10:  # 0.1초 * 10 = 1초
                    cycle_check_count = 0
                    self.modbus_queue.put({"mode": "alive", "value": 1})
                
                # PLC Alive 신호 체크
                if self.changed_modbus_signal[0]:
                    if self.recv_modbus_signal[0] == 1:
                        LM.log_print("[PLC] Alive ON")
                    elif self.recv_modbus_signal[0] == 0:
                        LM.log_print("[PLC] Alive OFF")
                    self.changed_modbus_signal[0] = False

                # 라인 모드 변경 신호 1: 자동 / 2: 수동
                if self.changed_modbus_signal[2]:
                    self.changed_modbus_signal[2] = False
                    if self.recv_modbus_signal[2] == 1:
                        self.manual_mode = False
                        LM.log_print("[PLC] Line mode: Auto")
                    elif self.recv_modbus_signal[2] == 2:
                        self.manual_mode = True
                        LM.log_print("[PLC] Line mode: Manual")

                # 모델 변경 신호
                if self.changed_modbus_signal[1]:
                    # 모든 클라이언트 연결 완료 전 or 수동 모드 아닌 경우 모델 변경 방지
                    if not SS.connect_complete or not self.manual_mode:
                        continue
                    
                    self.changed_modbus_signal[1] = False
                    if self.recv_modbus_signal[1] == 0:  # 0번 모델 변경 방지
                        continue
                    
                    self.model_number = str(self.recv_modbus_signal[1])
                    try:
                        self.model_name = model_info['model_mapping'][self.model_number]
                    except:
                        LM.log_print(f"[PLC] Model number {self.model_number} not found in model_info")
                        messagebox.showerror("모델 변경 에러", f"모델 {self.model_number}번에 대한 등록된 정보가 없습니다.\n관리자모드에서 {self.model_number}번 모델을 추가해주세요.")
                        continue

                    LM.log_print(f"[PLC] Model change order: {self.model_number}, Model name: {self.model_name}")

                    self.modbus_queue.put({"mode": "model", "value": self.recv_modbus_signal[1]})
                    self.modbus_queue.put({"mode": "busy"})

                    # 1. 모든 클라이언트 로드 완료 확인
                    for client_id in line_config['client_ids']:
                        MF.connect_complete_check(client_id, True)

                    # 2. JSON, 모델 정보 전송
                    SS.send_json_and_model()

                    # 3. 메인 프레임 설정
                    MF.main_canvas.itemconfig(MF.model_name_place, text=f"{self.model_name}")
                    MF.read_current_state()
                    MF.update_result_log()
                    
                # 검사 시작 신호
                if self.changed_modbus_signal[3]:
                    self.changed_modbus_signal[3] = False
                    if self.recv_modbus_signal[3] == 1:
                        LM.log_print("[PLC] Inspection start")
                        HW.reset_variables()
                        SS.send_msg_to_client("start")
                        self.inspection_start_time = time.time()
                        self.modbus_queue.put({"mode": "busy"})
                        self.modbus_queue.put({"mode": "state", "value": 1})
                
                # [4], [5] - 미사용

                # 검사 결과 요청 신호
                if self.changed_modbus_signal[6]:
                    self.changed_modbus_signal[6] = False
                    if self.recv_modbus_signal[6] == 1:
                        self.result_request = True
                        HW.analysis_result()
                        self.modbus_queue.put({"mode": "result_session", "value": 1})
                        LM.log_print("[PLC] Inspection result request")
                
                # PLC 확인 완료 신호
                if self.changed_modbus_signal[7]:
                    self.changed_modbus_signal[7] = False
                    if self.recv_modbus_signal[7] == 1:
                        LM.log_print("[PLC] PLC check complete")
                        self.modbus_queue.put({"mode": "ready"})
                        self.modbus_queue.put({"mode": "result_session", "value": 0})
                        self.modbus_queue.put({"mode": "result1", "value": 0})
                        self.modbus_queue.put({"mode": "result2", "value": 0})
                        self.modbus_queue.put({"mode": "state", "value": 0})
                
                # 비전 명령 1: 비전 초기화/ 2: 카운트 리셋/ 3: PC 재실행 / 4: x / 5: 불량 이력 초기화
                if self.changed_modbus_signal[8]:
                    self.changed_modbus_signal[8] = False
                    if self.recv_modbus_signal[8] == 1:
                        LM.log_print("[PLC] Vision reset")
                        self.modbus_queue.put({"mode": "busy"})
                        self.modbus_queue.put({"mode": "state", "value": 4})
                        # 작업 구현(미사용)

                        self.modbus_queue.put({"mode": "ready"})
                        self.modbus_queue.put({"mode": "state", "value": 0})

                    elif self.recv_modbus_signal[8] == 2:
                        LM.log_print("[PLC] Vision count reset")
                        self.modbus_queue.put({"mode": "busy"})
                        self.modbus_queue.put({"mode": "state", "value": 4})
                        
                        MF.count_reset('RESET')
                        MF.clear_ng_log_listboxes()

                        self.modbus_queue.put({"mode": "ready"})
                        self.modbus_queue.put({"mode": "state", "value": 0})

                    elif self.recv_modbus_signal[8] == 3:
                        LM.log_print("[PLC] PC reboot")
                        SS.send_msg_to_client("reboot")
                        os.system("shutdown -r") 
                    
                    elif self.recv_modbus_signal[8] == 5:
                        LM.log_print("[PLC] NG log reset")
                        self.modbus_queue.put({"mode": "busy"})
                        self.modbus_queue.put({"mode": "state", "value": 4})

                        MF.count_reset('NG_RESET')
                        MF.clear_ng_log_listboxes()

                        self.modbus_queue.put({"mode": "ready"})
                        self.modbus_queue.put({"mode": "state", "value": 0})

            except:
                LM.log_print(f"[MODBUS] Main loop error: {traceback.format_exc()}")
                self.is_connected = False
                time.sleep(1)

    def send_signal_thread(self):
        """PLC 신호 전송 스레드"""
        while True:
            if not self.modbus_device or not self.is_connected:
                time.sleep(0.1)
                continue
            
            try:
                command = self.modbus_queue.get(timeout=1)
            except:
                continue

            try:
                mode = command['mode']
                idx = command.get('value', 0)
                if mode != 'alive':
                    LM.log_print(f"[PLC] Signal sent: {mode}, Value: {idx}")
                
                if mode == "reset":  # 초기화
                    self.modbus_device.write_registers(address=200, values=[0,0,0,0,0,0,0,0,0,0,0])
                    
                elif mode == "reboot":  # 재부팅
                    self.modbus_device.write_registers(address=200, values=[0,0,0,0,0,0,0,0,0,2,0])
                    
                elif mode == "alive":  # 연결 확인
                    self.modbus_device.write_register(address=200, value=idx)
                    
                elif mode == "model":  # 모델 번호
                    self.modbus_device.write_register(address=201, value=idx)
                    
                elif mode == "line_mode":  # 라인 모드 # 1: 자동 / 2: 수동
                    self.modbus_device.write_register(address=202, value=idx)
                    
                elif mode == "ready":  # 준비 완료
                    self.modbus_device.write_register(address=203, value=1)
                    self.modbus_device.write_register(address=204, value=0)
                    
                elif mode == "busy":  # 작업중
                    self.modbus_device.write_register(address=203, value=0)
                    self.modbus_device.write_register(address=204, value=1)
                    
                elif mode == "result_session":  # 결과 종합
                    self.modbus_device.write_register(address=205, value=idx)
                    
                elif mode == "station1_result":  # 1번 스테이션 결과  # 1:중대불량 /2:일반불량 /3:양품 /4:데이터없음
                    self.modbus_device.write_register(address=206, value=idx)
                    
                elif mode == "station4_result":  # 4번 스테이션 결과  # 1:중대불량 /2:일반불량 /3:양품 /4:데이터없음
                    self.modbus_device.write_register(address=207, value=idx)
                    
                elif mode == "ng_continuity":  # 연속 불량 발생
                    self.modbus_device.write_register(address=208, value=idx)
                    
                elif mode == "state":  # 
                    self.modbus_device.write_register(address=209, value=idx)
                    
                elif mode == "reconnect":  #
                    self.modbus_device.write_registers(address=203, values=[1,0,0,0,0,0,0,0])
                    
                else:
                    LM.log_print(f"[PLC] Unknown mode: {mode}")
                        
            except:
                LM.log_print(f"[PLC] Signal processing error: {traceback.format_exc()}")
                self.is_connected = False
                break


# ▶ 작업 클래스
class HardWork:
    def __init__(self):
        # 라인 설정 로드
        self.inspection_sequence = line_config['sequence_map']
        self.first_station = line_config['stations']['first']
        self.second_station = line_config['stations']['second']
        
        # 스테이션 초기화
        self.station1_dict = {}
        self.station2_dict = {}
        self.station3_dict = {}
        self.station4_dict = {}

        try:
            self.hangul_font = ImageFont.truetype("C:/Windows/Fonts/malgunbd.ttf", 16)
        except:
            self.hangul_font = ImageFont.load_default()

    def update_labels(self, client_id, add_labels, remove_labels):
        """라벨 업데이트
        Args:
            client_id: 클라이언트 ID
            add_labels: 콤마로 구분된 추가할 라벨 문자열
            remove_labels: 콤마로 구분된 제거할 라벨 문자열
        """
        try:
            if add_labels:
                new_labels = add_labels.split(',')
                
                for label in new_labels:
                    if label not in model_info['models'][MB.model_name][client_id]['label_ng_conditions']:  # label_ng_conditions에 기본값으로 추가
                        model_info['models'][MB.model_name][client_id]['label_ng_conditions'][label] = ['미지정', 90, 2, 3]
            
            if remove_labels:
                remove_label_list = remove_labels.split(',')
                
                for label in remove_label_list:
                    if label in model_info['models'][MB.model_name][client_id]['critical_ng_list']:  # critical_ng_list에서 제거
                        model_info['models'][MB.model_name][client_id]['critical_ng_list'].remove(label)
                    
                    if label in model_info['models'][MB.model_name][client_id]['label_ng_conditions']:  # label_ng_conditions에서 제거
                        del model_info['models'][MB.model_name][client_id]['label_ng_conditions'][label]
                
            MF.save_info_json(model_info)
            SS.send_json()

            LM.log_print(f"[UPDATE] {client_id} Label Update Complete")
        except:
            LM.log_print(f'[UPDATE] {client_id} Label Update Failed: {traceback.format_exc()}')

    def reset_variables(self):
        """변수 초기화"""
        SS.result_dict = create_result_dict(line_config['client_ids'])

    def draw_text_on_image(self, image, text, position='top_left', color=(255, 255, 255), bg_color=(255, 0, 0)):
        """이미지에 텍스트를 그리는 함수
        position: 'top_left' 또는 'top_right'
        """
        # OpenCV 이미지를 PIL 이미지로 변환
        image_rgb = cv2.cvtColor(image, cv2.COLOR_BGR2RGB)
        pil_image = Image.fromarray(image_rgb)
        draw = ImageDraw.Draw(pil_image)
        
        # 텍스트 크기 및 폰트 메트릭 계산
        ascent, descent = self.hangul_font.getmetrics()
        bbox = draw.textbbox((0, 0), text, font=self.hangul_font)
        text_width = bbox[2] - bbox[0]
        text_height = bbox[3] - bbox[1]
        
        height, width = image.shape[:2]
        margin = 8  # 경계선과의 간격
        box_padding = 5  # 텍스트 박스 내부 여백
        
        if position == 'top_left':
            text_x = margin + box_padding
            text_y = margin + box_padding
        elif position == 'top_right':
            text_x = width - text_width - margin - box_padding
            text_y = margin + box_padding
        
        # 배경 박스 그리기
        box_x1 = text_x - box_padding
        box_y1 = text_y - box_padding
        box_x2 = text_x + text_width + box_padding
        box_y2 = text_y + text_height + box_padding
        draw.rectangle([box_x1, box_y1, box_x2, box_y2], fill=bg_color)
        
        # 텍스트 그리기
        draw.text((text_x, text_y-4), text, fill=color, font=self.hangul_font)
        
        # PIL 이미지를 다시 OpenCV 형식으로 변환
        return cv2.cvtColor(np.array(pil_image), cv2.COLOR_RGB2BGR)

    def make_show_image(self, client_id, label, image):
        """출력 이미지 만들기"""
        label = str(label).upper()
        # 색상 선택
        if label == 'NONE':
            color = (255, 255, 255)  # 흰색 (No data)
        elif 'OK' in label:
            color = (41, 252, 41)    # 초록색 (OK)
        else:
            color = (41, 41, 252)    # 빨간색 (NG)

        try:
            if label == 'NONE' or 'ERROR' in label:
                image = np.zeros((290, 391, 3), dtype=np.uint8)
                font = cv2.FONT_HERSHEY_SIMPLEX
                
                # 라벨에 따라 텍스트 결정
                text = 'Error' if 'ERROR' in label else 'No data'
                    
                textsize = cv2.getTextSize(text, font, 1, 2)[0]
                
                text_x = (image.shape[1] - textsize[0]) // 2
                text_y = (image.shape[0] + textsize[1]) // 2
                
                cv2.putText(image, text, (text_x, text_y), font, 1, (255, 255, 255), 2, cv2.LINE_AA)
            else:
                image = cv2.resize(image, (391, 290))

            height, width = image.shape[:2]
            image = cv2.rectangle(image, (0, 0), (width, height), color, 4)

            # GPU 상태가 False인 경우 이미지 우측 상단에 "GPU미사용" 표시
            if not SS.gpu_avail_dict[client_id]:
                image = self.draw_text_on_image(image, "GPU 미사용", position='top_right', color=(255, 0, 0), bg_color=(0, 0, 0))

            # 불량 정보를 좌측 상단에 표시
            if label != 'NONE' and 'OK' not in label and 'ERROR' not in label:
                # 불량 라벨에서 파트명과 불량명 추출
                if 'DETECTION' in label:
                    text_to_show = '각인 누락'
                    image = self.draw_text_on_image(image, text_to_show, position='top_left', color=(255, 255, 255), bg_color=(255, 0, 0))
                else:  # 일반 불량
                    client_data = model_info['models'][MB.model_name][client_id]
                    if 'label_ng_conditions' in client_data and label in client_data['label_ng_conditions']:
                        defect_name = client_data['label_ng_conditions'][label][0]
                    text_to_show = f"{defect_name}"
                    image = self.draw_text_on_image(image, text_to_show, position='top_left', color=(255, 255, 255), bg_color=(255, 0, 0))
                
            image = cv2.cvtColor(image, cv2.COLOR_BGR2RGBA)
            image = Image.fromarray(image)
            photo_image = ImageTk.PhotoImage(image)
            return photo_image
        except:
            LM.log_print(f"[MAKE] make show image error: {traceback.format_exc()}")
            image = np.zeros((290, 391, 3), dtype=np.uint8)
            image = cv2.rectangle(image, (0, 0), (391, 290), color, 4)
            image = cv2.cvtColor(image, cv2.COLOR_BGR2RGBA)
            image = Image.fromarray(image)
            return ImageTk.PhotoImage(image)

    def move_buffer(self):
        """버퍼 이동: station1 -> 2 -> 3 -> 4"""
        # station3 -> station4 이동
        self.station4_dict.update(self.station3_dict)
        
        # station2 -> station3 이동
        self.station3_dict = self.station2_dict.copy()
        
        # station1 -> station2 이동
        self.station2_dict = self.station1_dict.copy()
        
        # 현재 결과 -> station1 이동
        self.station1_dict = SS.result_dict.copy()

        # 각 스테이션 라벨 출력
        for name, d in [
            ("station1", self.station1_dict),
            ("station2", self.station2_dict),
            ("station3", self.station3_dict),
            ("station4", self.station4_dict),
            ("result_dict", SS.result_dict),
        ]:
            labels = {k: v.get('label', None) for k, v in d.items()}
            print(f"{name} labels: {labels}")

    def analysis_result(self):
        """검사 결과 종합"""
        all_present = all(
            v["label"] is not None and v["image"] is not None
            for v in SS.result_dict.values()
        )
        print(f"[RESULT] Check analysis conditions: all_present={all_present}, result_request={MB.result_request}")
        all_present = True  # 테스트용
        print(f"[RESULT] Check test analysis conditions: all_present={all_present}, result_request={MB.result_request}")  # 테스트용
        
        if MB.result_request and all_present:
            LM.log_print("[RESULT] results summary started!")

            if MB.manual_mode:  # 수동 검사
                self.display_results_images(SS.result_dict)  # 검사 결과 표시

            else:  # 자동 검사
                self.move_buffer()  # 버퍼 이동

                for client_id in self.first_station:
                    self.station1_dict[client_id] = SS.result_dict[client_id]
                
                for client_id in self.second_station:
                    self.station4_dict[client_id] = SS.result_dict[client_id]

                self._send_result_to_plc(self.station1_dict, self.station4_dict)  # PLC에 검사 결과 전송
                date_time = self.get_date_time()
                self.display_results_images(self.station4_dict)  # 검사 결과 표시
                self._print_results(self.station4_dict)  # 검사 결과 정리 및 출력
                MF.update_count(self.station4_dict)  # 카운트 업데이트
                is_critical_ng = self.check_critical_ng(self.station4_dict)  # 중대 불량 여부 확인
                DB.write_result(MB.model_name, is_critical_ng, date_time, self.station4_dict)  # 검사 결과 DB 저장
                MF.update_result_log()  # 검사 결과 로그 업데이트
            
            MB.result_request = False  # 결과 요청 신호 초기화
        
    def _send_result_to_plc(self, station1_dict, station4_dict):
        """PLC에 검사 결과 전송"""
        stations = {
            'station1': station1_dict,
            'station4': station4_dict
        }
        
        for station_name, result_dict in stations.items():
            final_result = 'ok'
            for client_id, result in result_dict.items():
                label = str(result['label']).upper()

                # 1. 배출 바이패스 여부 확인
                bypass_enabled = model_info['models'][MB.model_name][client_id].get('inspection_only', False)
                if bypass_enabled:
                    continue

                # 2. 중대 불량 여부 확인 
                critical_ng_list = [ng.upper() for ng in model_info['models'][MB.model_name][client_id]['critical_ng_list']]
                if label in critical_ng_list:
                    final_result = 'critical'
                    break
                    
                # 3. 데이터 없음 여부 확인
                elif label == 'NONE':
                    if final_result == 'ok':
                        final_result = 'none'
                
                # 4. 일반 불량 여부 확인
                elif 'OK' not in label:
                    final_result = 'ng'
                    
            if final_result == 'critical':  # 중대 불량 
                value = 1
            elif final_result == 'ng':  # 일반 불량
                value = 2
            elif final_result == 'none':  # 데이터 없음
                value = 4
            else:  # 양품
                value = 3
            
            MB.modbus_queue.put({"mode": station_name + '_result', "value": value})
            LM.log_print(f"[PLC] Send result: {station_name} {value}")
        
        MB.modbus_queue.put({"mode": "ready"})

    def get_date_time(self):
        """날짜와 시간 반환"""
        now = datetime.datetime.now()
        return now.strftime("%Y-%m-%d %H:%M:%S")

    def check_critical_ng(self, result_dict):
        """중대 불량 여부 확인"""
        for client_id, result in result_dict.items():
            if result['label'] in model_info['models'][MB.model_name][client_id]['critical_ng_list']:
                return True
        return False

    def display_results_images(self, result_dict):
        """결과 딕셔너리를 화면에 표시하는 공통 함수"""
        if not MF.ng_log_checking and not MF.ng_statistics_mode:  # 불량 로그 체크 중 or 불량 수량 확인 모드 활성화 중이면 출력 화면 업데이트 X
            for client_id, result in result_dict.items():
                label = result.get('label')
                image = result.get('image')
                idx = self.inspection_sequence[client_id]

                MF.show_image_list[idx] = self.make_show_image(client_id, label, image)
                MF.main_canvas.itemconfig(MF.show_place_list[idx], image=MF.show_image_list[idx], state='normal')
                MF.switch_ok_ng_sign(label, idx)

    def _print_results(self, final_station_dict):
        """검사 결과 정리 및 출력"""
        headers = line_config['client_ids']
        results = []
        for client_id in headers:
            if client_id in final_station_dict:
                label = final_station_dict[client_id].get('label')
                results.append(label if label is not None else '-')
            else:
                results.append('-')

        print("\nStation 4 Result:")
        print(tabulate([results], headers=headers, tablefmt='fancy_grid'))

    def check_critical_ng(self, final_station_dict):
        """중대 불량 여부 확인"""
        for client_id, result in final_station_dict.items():
            if result['label'] in model_info['models'][MB.model_name][client_id]['critical_ng_list']:
                return True
            
    def check_mail_send_time(self):
        """메일 전송 시간 확인 (08시 이후, 전날 데이터, 중복 전송 방지)"""
        while True:
            now = datetime.datetime.now()
            report_date = (now - datetime.timedelta(days=1)).date()  # 어제날짜로 항상 기록
            if now.hour >= 8 and not DB.already_sent_report(report_date):  # 08시 이후, 전날 데이터, 중복 전송 방지
                excel_path, start_date, end_date = ER.create_excel_report()
                try:
                    LM.log_print(f"[MAIL] Try to send daily report: {report_date}")
                    send_excel_report_with_context(
                        smtp_host="smtp.gmail.com",
                        smtp_port=465,
                        smtp_user="sslinesinplat@gmail.com",
                        smtp_password="iwppyeqlvjumzaoy",
                        sender="sslinesinplat@gmail.com",
                        recipients=["ooolov1@sinplat.com"],
                        line_name=line_name,
                        line_type=line_type,
                        start_date=start_date,
                        end_date=end_date,
                        excel_path=excel_path
                    )
                    DB.log_mail_send(report_date, 'Y', datetime.datetime.now())
                    LM.log_print(f"[MAIL] Successfully sent daily report: {report_date}")
                except Exception as e:
                    LM.log_print(f"[MAIL] Failed to send daily report: {e}")
                    DB.log_mail_send(report_date, 'N', datetime.datetime.now())
            time.sleep(60)  # 1분마다 체크


# ▶ 이력 조회 프레임 클래스
class HistoryFrame(tk.Frame):
    def __init__(self, master=None):
        super().__init__(master)
        self.master = master

        self.bg_image = ImageTk.PhotoImage(file=f"bg/{line_type}/history_bg.png")

        self.master.attributes("-fullscreen", True)
        self.master.bind("<F11>", lambda event: self.master.attributes("-fullscreen", not self.master.attributes("-fullscreen")))
        self.master.bind("<Escape>", lambda event: self.master.attributes("-fullscreen", False))
        
        self.create_widgets()
        
    def create_widgets(self):
        self.grid(row=0, column=0)
        self.history_canvas = tk.Canvas(self, width=1920, height=1080)
        self.BG = self.history_canvas.create_image(0, 0, image=self.bg_image, anchor="nw")

        self.font = ('Malgun Gothic', 14, 'bold')
        self.result_log_font = ('Malgun Gothic', 10)

        # 모델 선택 콤보박스
        self.model_combobox = tk.ttk.Combobox(self.history_canvas, font=('Malgun Gothic', 20, 'bold'), state='readonly', width=15)
        self.model_combobox.place(x=1646, y=164, anchor="center")
        
        # 모델 목록 로드
        self.load_model_list()
        
        # 모델 선택 이벤트 바인딩
        self.model_combobox.bind('<<ComboboxSelected>>', self.on_model_selected)

        # 시작 날짜 선택
        self.start_date_text = self.history_canvas.create_text(710, 986, text="시작 날짜:", font=self.font, fill='white', anchor='nw')
    
        self.start_date_entry = tk.Entry(self.history_canvas, font=self.font, width=10)
        self.start_date_entry.place(x=710, y=1010, anchor="nw")
        self.start_date_entry.insert(0, datetime.datetime.now().strftime("%Y-%m-%d"))
        
        self.start_date_button = tk.Button(self.history_canvas, text="달력", command=self.show_start_calendar,
                                          font=('Malgun Gothic', 10), bg='#4CAF50', fg='white')
        self.start_date_button.place(x=820, y=1010)

        # 종료 날짜 선택
        self.end_date_text = self.history_canvas.create_text(870, 986, text="종료 날짜:", font=self.font, fill='white', anchor='nw')

        self.end_date_entry = tk.Entry(self.history_canvas, font=self.font, width=10)
        self.end_date_entry.place(x=870, y=1010, anchor="nw")
        self.end_date_entry.insert(0, datetime.datetime.now().strftime("%Y-%m-%d"))
        
        self.end_date_button = tk.Button(self.history_canvas, text="달력", command=self.show_end_calendar,
                                        font=('Malgun Gothic', 10), bg='#4CAF50', fg='white')
        self.end_date_button.place(x=980, y=1010)

        # 불량명 선택 콤보박스
        self.defect_text = self.history_canvas.create_text(1030, 986, text="불량명:", font=self.font, fill='white', anchor='nw')
        
        self.defect_combobox = tk.ttk.Combobox(self.history_canvas, font=('Malgun Gothic', 13, 'bold'), state='readonly', width=15)
        self.defect_combobox.place(x=1030, y=1010, anchor="nw")

        # 검색 버튼
        self.search_button = tk.Button(self.history_canvas, text="검색", command=self.perform_search,
                                      font=self.font, bg='#4CAF50', fg='white', width=10)
        self.search_button.place(x=1230, y=992)

        # 카운트 표시
        self.total_count_place = self.history_canvas.create_text(1510, 319, text="0", font=self.font, fill='white', anchor='center')
        self.ok_count_place = self.history_canvas.create_text(1656, 319, text="0", font=self.font, fill='#51fc59', anchor='center')
        self.ng_count_place = self.history_canvas.create_text(1787, 319, text="0", font=self.font, fill='#ec5151', anchor='center')

        # 중대 불량 이력 리스트
        self.critical_ng_log = tk.Listbox(self.history_canvas, fg='white', bg='#2a5565', font=self.result_log_font, exportselection=False, selectmode='single')
        self.critical_ng_log.place(x=1427, y=406, width=206, height=631)
        self.critical_ng_log_scrollbar = tk.Scrollbar(self.history_canvas, bg='#2a5565', orient="vertical")
        self.critical_ng_log_scrollbar.config(command=self.critical_ng_log.yview)
        self.critical_ng_log_scrollbar.place(x=1618, y=406, width=15, height=631)
        self.critical_ng_log.config(yscrollcommand=self.critical_ng_log_scrollbar.set)
        self.critical_ng_log.bind('<<ListboxSelect>>', self.on_log_select)
        self.critical_ng_log.bind('<Up>', self.on_log_key)
        self.critical_ng_log.bind('<Down>', self.on_log_key)

        # 일반 불량 이력 리스트
        self.normal_ng_log = tk.Listbox(self.history_canvas, fg='white', bg='#2a5565', font=self.result_log_font, exportselection=False, selectmode='single')
        self.normal_ng_log.place(x=1660, y=406, width=206, height=631) 
        self.normal_ng_log_scrollbar = tk.Scrollbar(self.history_canvas, bg='#2a5565', orient="vertical")
        self.normal_ng_log_scrollbar.config(command=self.normal_ng_log.yview)
        self.normal_ng_log_scrollbar.place(x=1851, y=406, width=15, height=631)
        self.normal_ng_log.config(yscrollcommand=self.normal_ng_log_scrollbar.set)
        self.normal_ng_log.bind('<<ListboxSelect>>', self.on_log_select)
        self.normal_ng_log.bind('<Up>', self.on_log_key)
        self.normal_ng_log.bind('<Down>', self.on_log_key)

        # 이미지 출력 공간 선언
        self.show_image_list = [None] * client_num 
        self.show_place_list = [None] * client_num
        for i in range(client_num):
            if i < 3:
                self.show_place_list[i] = self.history_canvas.create_image(96+(i*441), 140, image='', anchor="nw", state="hidden")
            else :
                self.show_place_list[i] = self.history_canvas.create_image(96+((i-3)*441), 553, image='', anchor="nw", state="hidden")
        
        # OK, NG 표시 출력 공간 선언
        self.ok_sign_image = ImageTk.PhotoImage(file=f"bg/common/OK.png")
        self.ng_sign_image = ImageTk.PhotoImage(file=f"bg/common/NG.png")
        self.ok_sign_place_list = [None] * client_num
        self.ng_sign_place_list = [None] * client_num
        for i in range(client_num):
            if i < 3:
                self.ok_sign_place_list[i] = self.history_canvas.create_image(91+(i*441), 444, image = self.ok_sign_image, anchor="nw", state="hidden")
                self.ng_sign_place_list[i] = self.history_canvas.create_image(311+(i*441), 444, image = self.ng_sign_image, anchor="nw", state="hidden")
            else :
                self.ok_sign_place_list[i] = self.history_canvas.create_image(91+((i-3)*441), 857, image = self.ok_sign_image, anchor="nw", state="hidden")
                self.ng_sign_place_list[i] = self.history_canvas.create_image(311+((i-3)*441), 857, image = self.ng_sign_image, anchor="nw", state="hidden")

        self.history_canvas.bind("<Button-1>", self.main_btn)
        self.history_canvas.pack()

    def main_btn(self, event):
        """메인 버튼 클릭 이벤트"""
        x = event.x
        y = event.y
        
        if 1870 < x < 1912 and 11 < y < 53:
            print("program exit")
            MF.on_closing()
        
        elif 89 < x < 271 and 976 < y < 1051:
            print("main frame open")
            MF.tkraise()

        # 관리자 모드 클릭
        elif 459 < x < 641 and 976 < y < 1051:
            print("admin frame open")
            AF.tkraise()

    def load_model_list(self):
        """모델 목록을 콤보박스에 로드"""
        if 'model_mapping' in model_info:
            sorted_model_names = [
                model_info['model_mapping'][num]
                for num in sorted(model_info['model_mapping'], key=lambda x: int(x))
            ]
            self.model_combobox['values'] = sorted_model_names

    def load_defect_list(self):
        """불량명 목록을 콤보박스에 로드"""
        selected_model = self.model_combobox.get()
        if not selected_model or selected_model not in model_info['models']:
            self.defect_combobox['values'] = ['전체', '양품']
            return
        
        # 모든 클라이언트의 불량 라벨들을 수집
        all_defects = set()
        for client_id in line_config['client_ids']:
            if client_id in model_info['models'][selected_model]:
                client_data = model_info['models'][selected_model][client_id]
                if 'label_ng_conditions' in client_data:
                    for label, conditions in client_data['label_ng_conditions'].items():
                        if len(conditions) > 0:
                            all_defects.add(str(conditions[0]))  # 한글 이름을 문자열로 변환
        
        # 정렬하여 콤보박스에 설정 (모든 항목을 문자열로 변환하여 정렬)
        defect_list = [str(defect) for defect in all_defects]
        sorted_defects = ['전체', '양품'] + sorted(defect_list, key=str)
        self.defect_combobox['values'] = sorted_defects
        self.defect_combobox.set('전체')  # 기본값을 전체로 설정

    def show_start_calendar(self):
        """시작 날짜 달력 표시"""
        self.show_calendar(self.start_date_entry)

    def show_end_calendar(self):
        """종료 날짜 달력 표시"""
        self.show_calendar(self.end_date_entry)

    def show_calendar(self, entry_widget):
        """달력 팝업 표시"""
        def set_date():
            entry_widget.delete(0, tk.END)
            entry_widget.insert(0, cal.get_date())
            top.destroy()
        
        top = tk.Toplevel(self)
        top.title("날짜 선택")
        top.geometry("400x400")
        
        cal = Calendar(top, selectmode='day', date_pattern='yyyy-mm-dd')
        cal.pack(fill="both", expand=True)
        
        
        tk.Button(top, width=20, text="선택", font=('Malgun Gothic', 14), fg='black', command=set_date).pack(pady=10)

    def perform_search(self):
        """검색 실행"""
        # 선택된 모델 확인
        selected_model = self.model_combobox.get()
        if not selected_model:
            messagebox.showwarning("경고", "모델을 선택해주세요.")
            return
        
        # 날짜 형식 검증
        start_date = self.start_date_entry.get().strip()
        end_date = self.end_date_entry.get().strip()
        
        if not start_date or not end_date:
            messagebox.showwarning("경고", "시작 날짜와 종료 날짜를 입력해주세요.")
            return
        
        # 날짜 형식 검증
        try:
            start_datetime = datetime.datetime.strptime(start_date + " 00:00:00", "%Y-%m-%d %H:%M:%S")
            end_datetime = datetime.datetime.strptime(end_date + " 23:59:59", "%Y-%m-%d %H:%M:%S")
        except ValueError:
            messagebox.showerror("오류", "날짜 형식이 올바르지 않습니다. (YYYY-MM-DD)")
            return

        if start_datetime > end_datetime:
            messagebox.showerror("오류", "시작 날짜가 종료 날짜보다 늦을 수 없습니다.")
            return

        # 선택된 불량명 확인 (선택하지 않으면 모든 데이터 표시)
        selected_defect = self.defect_combobox.get()

        # 검색 실행
        self.search_results(selected_model, start_datetime, end_datetime, selected_defect)

    def search_results(self, model_name, start_datetime, end_datetime, defect_name):
        """검색 결과 조회 및 표시"""
        try:
            # DB에서 날짜 범위와 모델명으로 검색
            critical_results = DB.read_result_by_date_range('critical_results', start_datetime, end_datetime, model_name)
            normal_results = DB.read_result_by_date_range('normal_results', start_datetime, end_datetime, model_name)
            
            # 선택된 불량명에 해당하는 라벨 찾기
            target_labels = []
            if defect_name and defect_name not in ['전체', '양품']:  # 특정 불량명이 선택된 경우
                for client_id in line_config['client_ids']:
                    if client_id in model_info['models'][model_name]:
                        client_data = model_info['models'][model_name][client_id]
                        if 'label_ng_conditions' in client_data:
                            for label, conditions in client_data['label_ng_conditions'].items():
                                if len(conditions) > 0 and conditions[0] == defect_name:
                                    target_labels.append(label)
            
            # 결과 필터링 및 카운트
            total_count = 0
            ok_count = 0
            ng_count = 0
            
            critical_filtered = []
            normal_filtered = []
            
            # 중대 불량 결과 필터링
            for row in critical_results:
                should_include = False
                all_ok = True
                
                # 각 클라이언트의 결과 확인
                for client_id in line_config['client_ids']:
                    result_column = f"{client_id}_result"
                    if result_column in row and row[result_column]:
                        result_value = str(row[result_column]).upper()
                        if result_value == 'NONE' or 'ERROR' in result_value:
                            all_ok = False
                        elif ':' in result_value:
                            part_name, label = result_value.split(':', 1)
                            if 'OK' not in label:
                                all_ok = False
                
                # 필터링 조건에 따른 포함 여부 결정
                if defect_name == '전체':
                    should_include = True
                elif defect_name == '양품':
                    should_include = all_ok
                else:  # 특정 불량명
                    # 해당 불량이 있는지 확인
                    for client_id in line_config['client_ids']:
                        result_column = f"{client_id}_result"
                        if result_column in row and row[result_column]:
                            result_value = str(row[result_column]).upper()
                            if result_value != 'NONE' and ':' in result_value:
                                part_name, label = result_value.split(':', 1)
                                if label in target_labels:
                                    should_include = True
                                    break
                
                # 카운트 및 필터링
                if should_include:
                    critical_filtered.append(row)
                    if all_ok:
                        ok_count += 1
                    else:
                        ng_count += 1
                    total_count += 1
            
            # 일반 불량 결과 필터링
            for row in normal_results:
                should_include = False
                all_ok = True
                
                # 각 클라이언트의 결과 확인
                for client_id in line_config['client_ids']:
                    result_column = f"{client_id}_result"
                    if result_column in row and row[result_column]:
                        result_value = str(row[result_column]).upper()
                        if result_value == 'NONE' or 'ERROR' in result_value:
                            all_ok = False
                        elif ':' in result_value:
                            part_name, label = result_value.split(':', 1)
                            if 'OK' not in label:
                                all_ok = False
                
                # 필터링 조건에 따른 포함 여부 결정
                if defect_name == '전체':
                    should_include = True
                elif defect_name == '양품':
                    should_include = all_ok
                else:  # 특정 불량명
                    # 해당 불량이 있는지 확인
                    for client_id in line_config['client_ids']:
                        result_column = f"{client_id}_result"
                        if result_column in row and row[result_column]:
                            result_value = str(row[result_column]).upper()
                            if result_value != 'NONE' and ':' in result_value:
                                part_name, label = result_value.split(':', 1)
                                if label in target_labels:
                                    should_include = True
                                    break
                
                # 카운트 및 필터링
                if should_include:
                    normal_filtered.append(row)
                    if all_ok:
                        ok_count += 1
                    else:
                        ng_count += 1
                    total_count += 1
            
            # 카운트 업데이트
            self.history_canvas.itemconfig(self.total_count_place, text=str(total_count))
            self.history_canvas.itemconfig(self.ok_count_place, text=str(ok_count))
            self.history_canvas.itemconfig(self.ng_count_place, text=str(ng_count))
            
            # 로그 표시
            self.display_search_logs(critical_filtered, normal_filtered, model_name)
            
        except Exception as e:
            messagebox.showerror("오류", f"검색 중 오류가 발생했습니다: {traceback.format_exc()}")
            LM.log_print(f"[ERROR] History search failed: {traceback.format_exc()}")

    def display_search_logs(self, critical_results, normal_results, model_name):
        """검색 결과를 로그 형태로 표시"""
        # 기존 로그 삭제
        self.critical_ng_log.delete(0, tk.END)
        self.normal_ng_log.delete(0, tk.END)
        
        # 중대 불량 로그 표시
        for row in critical_results:
            self.add_log_entry(self.critical_ng_log, row, model_name)
        
        # 일반 불량 로그 표시
        for row in normal_results:
            self.add_log_entry(self.normal_ng_log, row, model_name)

    def add_log_entry(self, log_listbox, row, model_name):
        """로그 항목 추가"""
        # 불량이 있는 클라이언트들의 파트 정보 수집
        ng_parts = []
        none_parts = []
        critical_ng_parts = []
        all_ok = True
        
        for client_id in line_config['client_ids']:
            result_column = f"{client_id}_result"
            if result_column in row and row[result_column]:
                result_value = str(row[result_column]).upper()
                if result_value == 'NONE':
                    client_name = model_info['models'][model_name][client_id]['name']
                    none_parts.append(client_name)
                    all_ok = False
                elif ':' in result_value:
                    part_name, label = result_value.split(':', 1)
                    if 'OK' not in label:
                        client_name = model_info['models'][model_name][client_id]['name']
                        part_info = f"{client_name} {part_name}"
                        
                        # 중대불량 여부 확인
                        if log_listbox == self.critical_ng_log and label in model_info['models'][model_name][client_id]['critical_ng_list']:
                            critical_ng_parts.append(part_info)
                        else:
                            ng_parts.append(part_info)
                        all_ok = False
            else:
                client_name = model_info['models'][model_name][client_id]['name']
                none_parts.append(client_name)
                all_ok = False
        
        # 파트 정보 조합 (중대불량 우선)
        if log_listbox == self.critical_ng_log and critical_ng_parts:
            all_parts = critical_ng_parts + ng_parts + none_parts
            if len(all_parts) == 1:
                part_info = all_parts[0]
            else:
                part_info = f"{all_parts[0]} 외 {len(all_parts)-1}"
        elif ng_parts and none_parts:  # 불량과 미검사가 혼재 - 하나로 통합
            all_parts = ng_parts + none_parts
            if len(all_parts) == 1:
                part_info = all_parts[0]
            else:
                part_info = f"{all_parts[0]} 외 {len(all_parts)-1}"
        elif ng_parts:  # 불량만 있는 경우
            if len(ng_parts) == 1:
                part_info = ng_parts[0]
            else:
                part_info = f"{ng_parts[0]} 외 {len(ng_parts)-1}"
        elif none_parts:  # 미검사만 있는 경우
            if len(none_parts) == 1:
                part_info = f"{none_parts[0]} 미검사"
            else:
                part_info = f"{none_parts[0]} 외 {len(none_parts)-1}"
        else:  # 양품인 경우
            part_info = "전체"

        # 불량 타입 정보 수집
        ng_types = []
        for client_id in line_config['client_ids']:
            result_column = f"{client_id}_result"
            if result_column in row and row[result_column]:
                result_value = str(row[result_column]).upper()
                if result_value != 'NONE' and ':' in result_value:
                    part_name, label = result_value.split(':', 1)
                    if 'ERROR' in label:
                        ng_types.append('검사 오류')
                        break
                    elif 'OK' not in label:
                        for client_id_check in line_config['client_ids']:
                            if label in model_info['models'][model_name][client_id_check]['label_ng_conditions']:
                                korean_name = model_info['models'][model_name][client_id_check]['label_ng_conditions'][label][0]
                                ng_types.append(korean_name)
                                break
        
        # 불량 타입 조합
        if not ng_types and none_parts:
            ng_type = "미검사"
        elif not ng_types and all_ok:
            ng_type = "양품"
        elif len(ng_types) == 1:
            ng_type = ng_types[0]
        else:
            ng_type = f"{ng_types[0]} 외 {len(ng_types)-1}건"
        
        # 로그 형식: [시간] 파트 정보
        #           : 불량 타입
        log_time = row['input_time'].strftime('%H:%M:%S')
        
        # 첫 번째 줄 (시간 + 파트 정보)
        first_line = f"[{log_time}] {part_info}"
        # 두 번째 줄 (불량 타입)
        second_line = f"  : {ng_type}"
        
        # 양품인지 불량인지 판단하여 색상 결정
        is_ok = all_ok and not ng_parts and not critical_ng_parts and not none_parts
        
        # 리스트박스에 항목 추가 (색상은 태그로 처리)
        log_listbox.insert(tk.END, first_line)
        log_listbox.insert(tk.END, second_line)
        
        # 현재 리스트박스의 항목 수를 가져와서 인덱스 계산
        current_size = log_listbox.size()
        first_line_index = current_size - 2  # 첫 번째 줄 인덱스
        second_line_index = current_size - 1  # 두 번째 줄 인덱스
        
        # 색상 태그 적용 (Tkinter Listbox는 제한적이므로 배경색으로 구분)
        if is_ok:
            # 양품인 경우 초록색 배경
            log_listbox.itemconfig(second_line_index, {'bg': '#2d5a2d'})
            log_listbox.itemconfig(first_line_index, {'bg': '#2d5a2d'})
        else:
            # 불량인 경우 빨간색 배경
            log_listbox.itemconfig(second_line_index, {'bg': '#a40808'})
            log_listbox.itemconfig(first_line_index, {'bg': '#a40808'})

    def on_log_select(self, event):
        """로그 선택 이벤트 핸들러"""
        # 어떤 리스트박스에서 이벤트가 발생했는지 확인
        widget = event.widget
        
        # 클릭한 위치가 실제 항목인지 확인
        index = widget.nearest(event.y)
        if index < 0:
            # 빈 공간을 클릭한 경우 선택 해제
            widget.selection_clear(0, tk.END)
            return
        
        # 다른 리스트박스의 선택 해제
        if widget == self.critical_ng_log:
            self.normal_ng_log.selection_clear(0, tk.END)
        else:
            self.critical_ng_log.selection_clear(0, tk.END)
        
        if not widget.curselection():
            return
            
        selected_idx = widget.curselection()[0]
        pair_idx = selected_idx - (selected_idx % 2)  # 짝수 인덱스 (첫 번째 줄)
        
        # 선택된 항목들을 쌍으로 선택
        widget.selection_clear(0, tk.END)
        widget.selection_set(pair_idx)
        widget.selection_set(pair_idx + 1)
        
        # 로그에서 시간 추출
        log_line = widget.get(pair_idx)
        match = re.search(r"\[(\d{2}:\d{2}:\d{2})\]", log_line)
        if not match:
            return
        
        log_time = match.group(1)
        
        # 해당 테이블에서 로그 조회
        if widget == self.critical_ng_log:
            table_name = 'critical_results'
        else:
            table_name = 'normal_results'
        
        # DB에서 해당 시간의 로그 조회
        row = DB.get_result_by_time_from_table(log_time, table_name)
        if row:
            self.history_show_log_images_from_row(row)
        else:
            LM.log_print(f"[ERROR] No result found for time: {log_time} in {table_name}")

    def history_show_log_images_from_row(self, row):
        """DB 행 데이터에서 이미지 표시"""
        for client_id in line_config['client_ids']:
            result_column = f"{client_id}_result"
            path_column = f"{client_id}_path"
            
            # 결과와 이미지 경로 가져오기
            result_value = row.get(result_column, 'None')
            label = str(result_value.split(':')[1]).upper()
            image_path = row.get(path_column, 'None')
            
            # 표시 인덱스 가져오기
            display_idx = HW.inspection_sequence[client_id]
            
            # 이미지 생성 및 표시
            show_image = None
            
            # 결과가 None or error인 경우
            if label == 'NONE' or 'ERROR' in label:
                show_image = HW.make_show_image(client_id, label, None)
            else:  # 검사 결과 정상인 경우
                try:
                    abs_path = os.path.join('db', image_path)
                    image = cv2.imread(abs_path)
                    show_image = HW.make_show_image(client_id, label, image)
                except Exception as e:
                    LM.log_print(f"[ERROR] Failed to load image: {str(e)}")
                    show_image = HW.make_show_image(client_id, 'ERROR', None)
            
            # 캔버스에 이미지 표시
            self.show_image_list[display_idx] = show_image
            self.history_canvas.itemconfig(self.show_place_list[display_idx], 
                                       image=self.show_image_list[display_idx], 
                                       state='normal')
            
            # OK/NG 신호 표시
            self.switch_ok_ng_sign(label, display_idx)

    def switch_ok_ng_sign(self, label, display_idx):
        """OK, NG 표시 스위치"""
        label = str(label).upper()
        if label == 'NONE':
            self.history_canvas.itemconfig(self.ok_sign_place_list[display_idx], state='hidden')
            self.history_canvas.itemconfig(self.ng_sign_place_list[display_idx], state='hidden')
        elif 'OK' not in label:
            self.history_canvas.itemconfig(self.ok_sign_place_list[display_idx], state='hidden')
            self.history_canvas.itemconfig(self.ng_sign_place_list[display_idx], state='normal')
        else:
            self.history_canvas.itemconfig(self.ok_sign_place_list[display_idx], state='normal')
            self.history_canvas.itemconfig(self.ng_sign_place_list[display_idx], state='hidden')

    def on_model_selected(self, event):
        """모델 선택 이벤트 핸들러"""
        selected_model = self.model_combobox.get()
        if selected_model:
            # 불량명 목록 업데이트
            self.load_defect_list()
            print(f"Selected model: {selected_model}")

    def on_log_key(self, event):
        widget = event.widget
        size = widget.size()
        sel = widget.curselection()
        if not sel:
            return
        idx = sel[0] - (sel[0] % 2)
        if event.keysym == "Up":
            new_idx = max(0, idx - 2)
        elif event.keysym == "Down":
            new_idx = min(size - 2, idx + 2)
        else:
            return
        widget.selection_clear(0, tk.END)
        widget.selection_set(new_idx)
        widget.selection_set(new_idx + 1)
        widget.activate(new_idx)  # 커서를 첫 줄로 이동
        widget.see(new_idx)
        # 방향키 이동 시에도 on_log_select를 호출하여 이미지 등 갱신
        fake_event = type('Event', (object,), {'widget': widget, 'y': 0})()
        self.on_log_select(fake_event)

    def tkraise(self):
        """프레임 활성화 시 모델 목록과 불량명 목록 업데이트"""
        # 모델 목록 업데이트
        self.load_model_list()
        
        # 현재 선택된 모델이 있으면 불량명 목록도 업데이트
        if self.model_combobox.get():
            self.load_defect_list()
        
        super().tkraise()


# ▶ 관리자 프레임 클래스
class AdminFrame(tk.Frame):
    def __init__(self, master=None):
        super().__init__(master)
        self.master = master

        self.initial_settings = {}  # 초기 설정값 저장
        self.is_new_model_mode = False  # 신규 모델 등록 모드
        self.model_entry = None  # 모델명 입력 엔트리
        self.model_number_entry = None  # 모델 번호 입력 엔트리
        self.mapping_window = None  # 모델 매칭 관리 창

        self.bg_image = ImageTk.PhotoImage(file=f"bg/common/admin_bg.png")
        self.cancel_new_model_registration_btn_image = ImageTk.PhotoImage(file=f"bg/common/cancel_new_model_registration_btn.png")
        self.registration_btn_image = ImageTk.PhotoImage(file=f"bg/common/registration_btn.png")

        self.master.attributes("-fullscreen", True)
        self.master.bind("<F11>", lambda event: self.master.attributes("-fullscreen", not self.master.attributes("-fullscreen")))
        self.master.bind("<Escape>", lambda event: self.master.attributes("-fullscreen", False))
        
        # 모델 매칭 정보가 없으면 초기화
        if 'model_mapping' not in model_info:
            model_info['model_mapping'] = {}
        
        self.create_widgets()
        
    def create_widgets(self):
        self.grid(row=0, column=0)
        self.admin_canvas = tk.Canvas(self, width=1920, height=1080)
        self.BG = self.admin_canvas.create_image(0, 0, image=self.bg_image, anchor="nw")

        self.font = ('Malgun Gothic', 14, 'bold')

        # 모델 선택 콤보박스
        self.model_combobox = tk.ttk.Combobox(self.admin_canvas, font=self.font, state='readonly', width=15)
        self.model_combobox.place(x=1787, y=165, anchor="center")

        # 모델 번호
        self.model_number_place = self.admin_canvas.create_text(1841, 229, text="", font=self.font, fill='white')

        # 신규 형번 등록 이미지
        self.cancel_new_model_registration_place = self.admin_canvas.create_image(1683, 363, image=self.cancel_new_model_registration_btn_image, 
                                                                                  anchor="nw",state='hidden')
        
        # 저장 & 등록 버튼
        self.registration_place = self.admin_canvas.create_image(1678, 940, image=self.registration_btn_image, 
                                                                                  anchor="nw",state='hidden')
        
        # 모델 목록 로드
        self.load_model_list()
        
        # 모델 변경 이벤트 바인딩
        self.model_combobox.bind('<<ComboboxSelected>>', self.update_model_info_ui)
        
        # 클라이언트 설정 창들 생성
        self.update_model_info_ui()

        self.admin_canvas.bind("<Button-1>", self.main_btn)
        self.admin_canvas.pack()
    
    def load_model_list(self):
        """모델 목록을 콤보박스에 로드"""
        # model_mapping의 키(번호) 기준 오름차순 정렬
        sorted_model_names = [
            model_info['model_mapping'][num]
            for num in sorted(model_info['model_mapping'], key=lambda x: int(x))
        ]
        self.model_combobox['values'] = sorted_model_names

    def update_model_info_ui(self, event=None):
        """모델 변경 시 UI 전체 갱신"""
        # 1. 선택된 모델명 가져오기 (이벤트 객체가 전달되어도 콤보박스에서 직접 가져옴)
        selected_model = self.model_combobox.get()
        
        # 2. 모델 번호 찾기 및 표시 업데이트
        model_number = None
        for num, name in model_info['model_mapping'].items():
            if name == selected_model:
                model_number = num
                break
        
        if model_number is not None:
            self.admin_canvas.itemconfig(self.model_number_place, text=model_number)
        else:
            self.admin_canvas.itemconfig(self.model_number_place, text="매칭없음")
        
        # 3. 기존 창들 제거 (존재하는 경우에만)
        if hasattr(self, 'client_settings_windows') and self.client_settings_windows:
            for window in self.client_settings_windows.values():
                if window and hasattr(window, 'destroy'):
                    try:
                        window.destroy()
                    except:
                        pass  # 이미 제거된 경우 무시
        
        # 4. 새로운 창들 생성 (선택된 모델명으로)
        self.client_settings_windows = {}
        
        if selected_model and selected_model in model_info['models']:
            client_ids = [name for name in model_info['models'][selected_model].keys() 
                         if name != 'current_status']
            
            # 각 클라이언트별로 설정 창 생성
            for i, client_id in enumerate(client_ids):
                # 창 위치 계산 (화면에 여러 창을 배치)
                x_pos = 30 + (i % 3) * 540  
                y_pos = 135 + (i // 3) * 413  
                
                # 설정 창 생성
                settings_frame = ClientSettingsFrame(self.admin_canvas, selected_model, client_id, 
                                                   x_pos, y_pos)
                self.client_settings_windows[client_id] = settings_frame

    def main_btn(self, event):
        """메인 버튼 클릭 이벤트"""
        x = event.x
        y = event.y
        
        if 1870 < x < 1912 and 11 < y < 53:
            print("program exit")
            MF.on_closing()
        
        elif 89 < x < 271 and 976 < y < 1051:
            print("main frame open")
            if self.has_settings_changed():
                result = messagebox.askyesno("확인", "설정이 저장되지않았습니다.\n저장하지 않고 페이지를 이동하시겠습니까?")
                if result:
                    MF.tkraise()
            else:
                MF.tkraise()
        
        # 이력 조회 버튼 클릭
        elif 274 < x < 456 and 976 < y < 1051:
            print("history frame open")
            if self.has_settings_changed():
                result = messagebox.askyesno("확인", "설정이 저장되지않았습니다.\n저장하지 않고 페이지를 이동하시겠습니까?")
                if result:
                    HF.tkraise()    
            else:
                HF.tkraise()

        # 저장 버튼
        elif 1675 < x < 1889 and 937 < y < 1053:
            result = messagebox.askyesno("확인", "설정을 저장하시겠습니까?")
            if result:
                print("client settings save")
                self.save_client_settings()

        # 형번 확인
        elif 1681 < x < 1893 and 278 < y < 355:
            print("model number check")
            self.open_model_mapping_window()
        
        # 신규 형번 등록&취소 버튼
        elif 1681 < x < 1893 and 361 < y < 438:
            print("new model registration")
            self.new_model_registration()
        
        # 형번 삭제
        elif 1681 < x < 1893 and 444 < y < 521:
            print("model delete")
            result = messagebox.askyesno("확인", f"{self.model_combobox.get()}형번 정보를 삭제하시겠습니까?")
            if result:
                self.delete_selected_model()
        
        # 코드 업데이트
        elif 1681 < x < 1893 and 527 < y < 604:
            print("code update")
            self.update_code()

    def update_code(self):
        """코드 안전 업데이트"""
        def on_rm_error(func, path, exc_info):
            os.chmod(path, stat.S_IWRITE)
            func(path)

        result = messagebox.askyesno("최종 확인", "코드를 업데이트하시겠습니까?")
        SS.send_msg_to_client("code_update")
        
        if not result:
            LM.log_print(f"[UPDATE] code update canceled")
            return

        LM.log_print('[UPDATE] Admin code update order')
        repo_name = f'Main_{line_type.upper()}'
        git_url = f'https://github.com/KRThor/{repo_name}.git' # 코드 업데이트할 깃허브 주소
        tmp_dir = "update_tmp"
        try:
            # 1. 임시 폴더에 다운로드
            if os.path.exists(tmp_dir):
                shutil.rmtree(tmp_dir, onerror=on_rm_error)
            self.git_clone(git_url, tmp_dir)  # git clone 또는 zip 다운로드/압축해제

            # 2. 새 Main.py가 정상적으로 존재하는지 검증
            new_main_path = os.path.join(tmp_dir, "Main.py")
            if not os.path.exists(new_main_path):
                raise Exception("다운로드한 Main.py가 존재하지 않습니다.")

            # 3. 기존 Main.py 백업
            if os.path.exists('Main_.py'):
                os.remove('Main_.py')
            if os.path.exists('Main.py'):
                os.rename('Main.py', 'Main_.py')

            # 4. 새 Main.py로 교체
            shutil.move(new_main_path, 'Main.py')
            shutil.rmtree(tmp_dir, onerror=on_rm_error)

            py_compile.compile("Main.py", cfile="Main.pyc")
            LM.log_print(f"[UPDATE] {repo_name} code compile success")
            messagebox.showinfo("성공", f"{repo_name} 코드 업데이트 완료\n프로그램을 재시작해주세요.")
        except Exception as e:
            LM.log_print(f"[UPDATE] {repo_name} code update failed: {traceback.format_exc()}")
            messagebox.showerror("실패", f"코드 업데이트 실패: {e}")
            
    def git_clone(self, git_url, target_dir):
        """git_url을 target_dir(임시 폴더 등)에 clone"""
        def on_rm_error(func, path, exc_info):
            os.chmod(path, stat.S_IWRITE)
            func(path)
            
        if os.path.exists(target_dir):  # 이미 있으면 삭제
            shutil.rmtree(target_dir, onerror=on_rm_error)
        os.makedirs(target_dir, exist_ok=True)
        git.Repo.clone_from(git_url, target_dir)
        
    def open_model_mapping_window(self):
        """모델 매칭 관리 창 열기"""
        # 기존 창이 열려있으면 닫기
        if self.mapping_window is not None:
            try:
                self.mapping_window.destroy()
            except:
                pass  # 이미 닫힌 경우 무시
            self.mapping_window = None
        
        # 새 창 생성
        self.mapping_window = tk.Toplevel(self)
        self.mapping_window.title("모델 매칭 관리")
        self.mapping_window.geometry("600x600")
        self.mapping_window.configure(bg='#2a5565')
        
        # 창이 닫힐 때 변수 초기화
        def on_window_close():
            window_to_destroy = self.mapping_window
            self.mapping_window = None
            window_to_destroy.destroy()
        
        self.mapping_window.protocol("WM_DELETE_WINDOW", on_window_close)
        
        # 스크롤 가능한 프레임
        canvas = tk.Canvas(self.mapping_window, bg='#2a5565')
        scrollbar = tk.Scrollbar(self.mapping_window, orient="vertical", command=canvas.yview)
        scrollable_frame = tk.Frame(canvas, bg='#2a5565')
        
        scrollable_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )
        
        canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        
        # 기존 형번 매칭 정보 표시
        mapping_label = tk.Label(scrollable_frame, text="현재 형번 매칭:", 
                                font=('Malgun Gothic', 14, 'bold'), bg='#2a5565', fg='white')
        mapping_label.pack(anchor=tk.W, padx=10, pady=5)
        
        # 오름차순 정렬하여 표시
        for model_number in sorted(model_info['model_mapping'], key=lambda x: int(x)):
            model_name = model_info['model_mapping'][model_number]
            row_frame = tk.Frame(scrollable_frame, bg='#2a5565')
            row_frame.pack(anchor=tk.W, padx=20, pady=2)
            tk.Label(row_frame, text=f"번호 {model_number} →", font=('Malgun Gothic', 12), bg='#2a5565', fg='white').pack(side=tk.LEFT)
            model_entry = tk.Entry(row_frame, font=('Malgun Gothic', 12), width=20, readonlybackground='#2a5565', fg='white', bd=0, highlightthickness=0, relief='flat', state='readonly')
            model_entry.pack(side=tk.LEFT)
            model_entry.configure(state='normal')
            model_entry.insert(0, model_name)
            model_entry.configure(state='readonly')
        
        # 형번 매칭 수정
        add_frame = tk.Frame(scrollable_frame, bg='#2a5565')
        add_frame.pack(fill=tk.X, padx=10, pady=10)
        
        tk.Label(add_frame, text="형번 매칭 수정:", 
                font=('Malgun Gothic', 14, 'bold'), bg='#2a5565', fg='white').pack(anchor=tk.W)
        
        input_frame = tk.Frame(add_frame, bg='#2a5565')
        input_frame.pack(anchor=tk.W, pady=5)
        
        tk.Label(input_frame, text="모델 번호:", font=('Malgun Gothic', 12), bg='#2a5565', fg='white').pack(side=tk.LEFT)
        number_entry = tk.Entry(input_frame, font=('Malgun Gothic', 12), width=8)
        number_entry.pack(side=tk.LEFT, padx=5)
        
        tk.Label(input_frame, text="모델명:", font=('Malgun Gothic', 12), bg='#2a5565', fg='white').pack(side=tk.LEFT, padx=(10,0))
        model_entry = tk.Entry(input_frame, font=('Malgun Gothic', 10), width=20)
        model_entry.pack(side=tk.LEFT, padx=5)

        def update_mapping():
            """형번 관리에서 수정 버튼 클릭 시 실행"""
            try:
                model_number = int(number_entry.get())
                model_name = model_entry.get().strip()

                if not model_name:
                    messagebox.showerror("오류", "모델명을 입력해주세요.")
                    self.mapping_window.lift()
                    self.mapping_window.focus_force()
                    return

                # 기존에 이 번호에 매핑된 모델명
                old_model_name = model_info['model_mapping'].get(str(model_number), None)
                
                # 같은 번호에 다른 모델명을 매핑하려는 경우 확인
                if old_model_name and old_model_name != model_name:
                    result = messagebox.askyesno(
                        "확인", 
                        f"번호 {model_number}에 이미 '{old_model_name}'이 매핑되어 있습니다.\n"
                        f"'{model_name}'으로 변경하시겠습니까?\n\n"
                        f"기존 매핑: {model_number} → {old_model_name}\n"
                        f"새 매핑: {model_number} → {model_name}"
                    )
                    if not result:
                        return

                # 이미 다른 번호에 매핑되어 있으면 기존 매핑 삭제(이동)
                to_delete = None
                for num, name in model_info['model_mapping'].items():
                    if name == model_name and str(model_number) != num:
                        to_delete = num
                        break

                if to_delete is not None:
                    result = messagebox.askyesno(
                        "확인",
                        f"모델명 '{model_name}'이 번호 {to_delete}에 이미 매핑되어 있습니다.\n"
                        f"번호 {to_delete}의 매핑을 삭제하고 번호 {model_number}로 이동하시겠습니까?\n\n"
                        f"기존: {to_delete} → {model_name}\n"
                        f"변경: {model_number} → {model_name}"
                    )
                    if not result:
                        return
                    del model_info['model_mapping'][to_delete]

                # 모델명 변경: models의 key도 같이 변경
                if old_model_name and old_model_name != model_name:
                    # models에 old_model_name이 있으면 key를 model_name으로 변경
                    if old_model_name in model_info['models']:
                        model_info['models'][model_name] = model_info['models'].pop(old_model_name)

                model_info['model_mapping'][str(model_number)] = model_name

                # 수정한 모델 번호가 현재 사용중인 모델인 경우 전체 정보 갱신
                if str(model_number) == str(MB.model_number):
                    MB.model_name = model_info['model_mapping'][str(model_number)]
                    MF.main_canvas.itemconfig(MF.model_name_place, text=MB.model_name)
                    self.model_combobox.set(MB.model_name)
                else:  # 콤보박스만 갱신
                    # 현재 선택된 모델이 바뀐 모델인지 확인 (old_model_name과 비교)
                    if old_model_name and self.model_combobox.get() == old_model_name:
                        # 콤보박스 선택을 새 이름으로 변경
                        self.model_combobox.set(model_name)
                
                # JSON 파일에 저장
                MF.save_info_json(model_info)
                SS.send_json()
                
                # 성공 메시지 표시
                messagebox.showinfo("성공", f"모델 매핑이 수정되었습니다.\n{model_number} → {model_name}")
                
                self.load_model_list()
                self.update_model_info_ui()

                # 창을 닫지 않고 최신화
                self.open_model_mapping_window()

            except ValueError:
                messagebox.showerror("오류", "모델 번호는 숫자로 입력해주세요.")
                self.mapping_window.lift()
                self.mapping_window.focus_force()
                return

        add_button = tk.Button(input_frame, text="수정", command=update_mapping,
                              font=('Malgun Gothic', 10), bg='#4CAF50', fg='white')
        add_button.pack(side=tk.LEFT, padx=10)
        
        # 매칭 삭제
        delete_frame = tk.Frame(scrollable_frame, bg='#2a5565')
        delete_frame.pack(fill=tk.X, padx=10, pady=10)
        
        tk.Label(delete_frame, text="형번 삭제:", 
                font=('Malgun Gothic', 14, 'bold'), bg='#2a5565', fg='white').pack(anchor=tk.W)
        
        delete_input_frame = tk.Frame(delete_frame, bg='#2a5565')
        delete_input_frame.pack(anchor=tk.W, pady=5)
        
        tk.Label(delete_input_frame, text="모델 번호:", font=('Malgun Gothic', 12), bg='#2a5565', fg='white').pack(side=tk.LEFT)
        delete_number_entry = tk.Entry(delete_input_frame, font=('Malgun Gothic', 12), width=8)
        delete_number_entry.pack(side=tk.LEFT, padx=5)
        
        def delete_mapping():
            try:
                model_number = delete_number_entry.get()
                if model_number in model_info['model_mapping']:
                    model_name = model_info['model_mapping'][model_number]
                    result = messagebox.askyesno("확인", f"매칭을 삭제하시겠습니까?\n{model_number} → {model_name}")
                    if result:
                        del model_info['model_mapping'][model_number]
                        
                        # JSON 파일에 저장
                        MF.save_info_json(model_info)
                        SS.send_json()
                        
                        messagebox.showinfo("성공", "매칭이 삭제되었습니다.")
                        self.open_model_mapping_window()  # 창을 닫지 않고 최신화
                else:
                    messagebox.showerror("오류", "해당 모델 번호의 매칭이 존재하지 않습니다.")
                    self.mapping_window.lift()
                    self.mapping_window.focus_force()
                    return
                
            except Exception as e:
                messagebox.showerror("오류", f"삭제 중 오류가 발생했습니다: {str(e)}")
                self.mapping_window.lift()
                self.mapping_window.focus_force()
                return
            
        delete_button = tk.Button(delete_input_frame, text="삭제", command=delete_mapping,
                                 font=('Malgun Gothic', 10), bg='#f44336', fg='white')
        delete_button.pack(side=tk.LEFT, padx=10)
        
        # 닫기 버튼
        close_button = tk.Button(self.mapping_window, text="닫기", command=on_window_close,
                                font=('Malgun Gothic', 12, 'bold'), bg='#666666', fg='white')
        close_button.place(relx=0.5, rely=0.97, anchor="s")
        
        canvas.pack(side="left", fill="both", expand=True, padx=10, pady=10)
        scrollbar.pack(side="right", fill="y")
    
    def get_model_by_number(self, model_number):
        """모델 번호로 모델명을 가져오기"""
        model_number_str = str(model_number)
        if model_number_str in model_info['model_mapping']:
            return model_info['model_mapping'][model_number_str]
        else:
            print(f"[WARNING] Model number {model_number} not found in mapping")
            return None
    
    def save_client_settings(self):
        """모든 클라이언트 설정을 한번에 저장"""
        try:
            # 신규 모델 등록 모드인 경우 새로운 모델명과 번호 확인
            if self.is_new_model_mode:
                new_model_name = self.model_entry.get().strip()
                new_model_number = self.model_number_entry.get().strip()

                if not new_model_name or new_model_name == "새 모델명 입력":
                    messagebox.showerror("오류", "새로운 모델명을 입력해주세요.")
                    return

                if not new_model_number or new_model_number == "번호":
                    messagebox.showerror("오류", "모델 번호를 입력해주세요.")
                    return
                
                try:
                    new_model_number = int(new_model_number)
                except ValueError:
                    messagebox.showerror("오류", "모델 번호는 숫자로 입력해주세요.")
                    return
                
                # 모델명 중복 확인
                if new_model_name in model_info['models']:
                    result = messagebox.askyesno("확인", f"모델명 '{new_model_name}'이 이미 존재합니다.\n덮어쓰시겠습니까?")
                    if not result:
                        return
                
                # 모델 번호 중복 확인
                if str(new_model_number) in model_info['model_mapping']:
                    result = messagebox.askyesno("확인", f"모델 번호 '{new_model_number}'이 이미 사용 중입니다.\n덮어쓰시겠습니까?")
                    if not result:
                        return
            
            # 모든 클라이언트 설정 창에서 저장 실행
            for client_id, settings_frame in self.client_settings_windows.items():
                print(f"[SAVE] Saving settings for client: {client_id}")
                
                save_result = settings_frame.save_settings()
                if not save_result:
                    return  # 저장 중단
            
            # 신규 모델 등록 모드인 경우 새로운 모델을 model_info에 추가
            if self.is_new_model_mode:
                new_model_name = self.model_entry.get().strip()
                new_model_number = int(self.model_number_entry.get().strip())
                
                # 새로운 모델 데이터 생성
                new_model_data = {
                    'current_status': '신규 등록'
                }
                
                # 각 클라이언트의 설정을 새로운 모델에 추가
                for client_id, settings_frame in self.client_settings_windows.items():
                    new_model_data[client_id] = settings_frame.client_data
                
                # model_info에 새로운 모델 추가
                model_info['models'][new_model_name] = new_model_data
                
                # 모델 매칭에 추가
                model_info['model_mapping'][str(new_model_number)] = new_model_name
                
                # 신규 모델 등록 모드 종료
                self.is_new_model_mode = False
                self.admin_canvas.itemconfig(self.cancel_new_model_registration_place, state='hidden')
                self.admin_canvas.itemconfig(self.registration_place, state='hidden')
                
                # 엔트리를 콤보박스로 변경
                self.switch_to_model_combobox()
                
                # 모델 목록 업데이트
                self.load_model_list()
                
                # 새로 생성된 모델 선택
                self.model_combobox.set(new_model_name)
                self.update_model_info_ui()
                
                print(f"[SAVE] New model '{new_model_name}' (number: {new_model_number}) created successfully")

            if self.is_new_model_mode:
                messagebox.showinfo("성공", f"새로운 모델 '{new_model_name}'이 생성되었습니다.")
            else:
                messagebox.showinfo("성공", "모든 클라이언트 설정이 저장되었습니다.")

            for client_id in line_config['client_ids']:
                if not SS.load_complete_check_dict[client_id]:
                    MF.save_info_json(model_info)
                    SS.send_json_and_model(client_id)  # 모델 로드 실패한 클라이언트는 모델 로드부터 전부 재시도
                    print(f"[SAVE]  Previous {client_id} model failed, retrying")
                else:  # 모델 로드 성공한 클라이언트는 설정만 저장
                    MF.save_info_json(model_info)
                    SS.send_json()
                    print(f"[SAVE] {client_id} model json save and send")

            # 다시 표시
            self.update_model_info_ui()

            print("[SAVE] All client settings saved successfully")
            
        except Exception as e:
            messagebox.showerror("오류", f"설정 저장 중 오류가 발생했습니다: {str(e)}")
            print(f"[ERROR] Failed to save client settings: {str(e)}")

    def has_settings_changed(self):
        """설정이 변경되었는지 확인 - 현재 UI 설정과 JSON 파일 내용 비교
        저장되지않은 설정이 있으면 True, 저장된거면 False"""
        try:
            # 현재 UI의 설정값들을 가져오기
            current_ui_settings = {}
            for client_id, settings_frame in self.client_settings_windows.items():
                current_ui_settings[client_id] = settings_frame.get_settings()
            
            # 현재 선택된 모델
            selected_model = self.model_combobox.get()
            if not selected_model or selected_model not in model_info['models']:
                return False
            
            # JSON 파일의 현재 설정과 비교
            json_settings = {}
            for client_id in model_info['models'][selected_model].keys():
                if client_id != 'current_status':
                    json_settings[client_id] = model_info['models'][selected_model][client_id]
            
            # 차이점 출력
            changed = False
            for client_id in current_ui_settings:
                if client_id not in json_settings:
                    print(f"[DIFF] {client_id} - UI에만 존재")
                    changed = True
                elif current_ui_settings[client_id] != json_settings[client_id]:
                    print(f"[DIFF] {client_id} - 값이 다름")
                    for k in current_ui_settings[client_id]:
                        v1 = current_ui_settings[client_id][k]
                        v2 = json_settings[client_id].get(k, None)
                        if v1 != v2:
                            print(f"    {k}: UI={v1} / JSON={v2}")
                    changed = True
            for client_id in json_settings:
                if client_id not in current_ui_settings:
                    print(f"[DIFF] {client_id} - JSON에만 존재")
                    changed = True
            return changed
            
        except Exception as e:
            print(f"[ERROR] Error checking settings change: {str(e)}")
            return True  # 오류 발생 시 변경된 것으로 간주

    def tkraise(self):
        """프레임 활성화 시 원본 설정값으로 초기화"""
        # 현재 모델의 설정창들 다시 생성
        if MB.model_name:
            self.model_combobox.set(MB.model_name)
            self.update_model_info_ui()
        
            super().tkraise()

    def new_model_registration(self):
        """신규 형번 등록 모드 토글"""
        if not self.is_new_model_mode:
            # 신규 모델 등록 모드 시작
            self.is_new_model_mode = True
            self.admin_canvas.itemconfig(self.cancel_new_model_registration_place, state='normal')
            self.admin_canvas.itemconfig(self.registration_place, state='normal')

            # 콤보박스를 엔트리로 변경
            self.switch_to_model_entry()
            
            # 클라이언트 설정창들을 기본값으로 초기화
            self.initialize_client_settings_with_defaults()
            
        else:
            # 신규 모델 등록 모드 종료
            self.is_new_model_mode = False
            self.admin_canvas.itemconfig(self.cancel_new_model_registration_place, state='hidden')
            self.admin_canvas.itemconfig(self.registration_place, state='hidden')

            # 엔트리를 콤보박스로 변경
            self.switch_to_model_combobox()
            
            # 원래 모델로 복원
            self.model_combobox.set(MB.model_name)
            self.update_model_info_ui()

    def switch_to_model_entry(self):
        """콤보박스를 엔트리로 변경"""
        # 기존 콤보박스 숨기기
        self.model_combobox.place_forget()
        
        # 모델명 엔트리 생성
        self.model_entry = tk.Entry(self.admin_canvas, font=self.font, width=16)
        self.model_entry.place(x=1787, y=165, anchor="center")
        self.model_entry.insert(0, "새 모델명 입력")
        
        # 모델 번호 엔트리 생성 (모델명 아래에 배치)
        self.model_number_entry = tk.Entry(self.admin_canvas, font=self.font, width=6)
        self.model_number_entry.place(x=1841, y=229, anchor="center")
        
    def switch_to_model_combobox(self):
        """엔트리를 콤보박스로 변경"""
        # 엔트리 제거
        if self.model_entry:
            self.model_entry.destroy()
            self.model_entry = None
        
        if self.model_number_entry:
            self.model_number_entry.destroy()
            self.model_number_entry = None
        
        # 콤보박스 다시 표시
        self.model_combobox.place(x=1787, y=165, anchor="center")

    def initialize_client_settings_with_defaults(self):
        """클라이언트 설정창들을 기본값으로 초기화"""
        # 기존 창들 제거
        for window in self.client_settings_windows.values():
            window.destroy()
        
        # 새로운 창들 생성 (기본값으로)
        self.create_client_settings_windows_with_defaults()

    def create_client_settings_windows_with_defaults(self):
        """기본값으로 클라이언트 설정 창들 생성"""
        self.client_settings_windows = {}
        
        # 기본 클라이언트 ID들 (line_config에서 가져오기)
        client_ids = line_config['client_ids']
        
        # 각 클라이언트별로 설정 창 생성
        for i, client_id in enumerate(client_ids):
            # 창 위치 계산 (화면에 여러 창을 배치)
            x_pos = 30 + (i % 3) * 540  
            y_pos = 135 + (i // 3) * 413  
            
            # 기본값 모드로 설정 창 생성
            settings_frame = ClientSettingsFrame(self.admin_canvas, "", client_id, x_pos, y_pos, is_default_mode=True)
            self.client_settings_windows[client_id] = settings_frame

    def delete_selected_model(self):
        """
        AdminFrame에서 현재 선택된 모델명을 info.json의 models와 model_mapping에서 삭제.
        단, 현재 메인화면에서 사용중인 모델은 삭제하지 않음.
        """
        selected_model = self.model_combobox.get()

        # 현재 사용중인 모델명 (MB.model_name, 혹은 MF에서 사용중인 모델)
        if selected_model == MB.model_name:
            messagebox.showwarning("경고", "현재 사용중인 모델은 삭제할 수 없습니다.")
            return

        # model_mapping에서 해당 모델명에 해당하는 번호(들) 찾기
        numbers_to_delete = [num for num, name in model_info['model_mapping'].items() if name == selected_model]
        if not numbers_to_delete:
            messagebox.showerror("오류", "선택된 모델의 매핑이 존재하지 않습니다.")
            return

        # 삭제 확인
        result = messagebox.askyesno("확인", f"모델 '{selected_model}'을(를) 완전히 삭제하시겠습니까?")
        if not result:
            return

        # models에서 삭제
        if selected_model in model_info['models']:
            del model_info['models'][selected_model]

        # model_mapping에서 삭제
        for num in numbers_to_delete:
            del model_info['model_mapping'][num]

        # JSON 파일에 저장
        MF.save_info_json(model_info)
        SS.send_json()

        messagebox.showinfo("성공", f"모델 '{selected_model}'이(가) 삭제되었습니다.")

        # 최신 데이터로 다시 로드 및 UI 갱신
        self.load_model_list()
        
        # 콤보박스 선택을 현재 사용중인 모델로 변경
        self.model_combobox.set(MB.model_name)
        self.update_model_info_ui()


# ▶ 관리자 - 클라이언트 설정 프레임 클래스 (캔버스 내 배치용)
class ClientSettingsFrame:
    def __init__(self, canvas, model_name, client_id, x_pos, y_pos, is_default_mode=False):
        self.canvas = canvas
        self.model_name = model_name
        self.client_id = client_id
        self.x_pos = x_pos
        self.y_pos = y_pos
        self.is_default_mode = is_default_mode
        
        # 기본값 모드인 경우 기본 설정값 사용, 아닌 경우 기존 데이터 사용
        if self.is_default_mode:
            self.client_data = self.get_default_settings()
        else:
            self.client_data = model_info['models'][model_name][client_id]
        
        self.create_widgets()
        self.load_current_settings()
    
    def get_default_settings(self):
        """클라이언트별 기본 설정값 반환"""
        return {
            'name': f"{self.client_id} 클라이언트",
            'detection_use': False,
            'detection_frame': [],
            'inspection_only': False,
            'origin_image_capture': True,
            'ng_image_capture': True,
            'inspection_image_capture': True,
            'show_coord': [0, 0, 100, 100],
            'detection_coords': [0, 0, 100, 100],
            'inspection_coords': {'n시': ["", 0, 0, 100, 100, 180],
                                  '케이지': ["_sub", 0, 0, 100, 100, 180]},
            'ok_engrave': 4,
            'inspection_frame': 21,
            'critical_ng_list': [],
            'label_ng_conditions': {}
        }
    
    def create_widgets(self):
        """위젯 생성"""
        # 메인 프레임 (기본값 모드일 때 노란색 테두리)
        if self.is_default_mode:
            self.frame = tk.Frame(self.canvas, bg='#2a5565', relief=tk.RAISED, bd=3, highlightbackground='yellow', highlightthickness=2)
            title_text = f"신규 등록: {self.client_id}"
            title_color = 'yellow'
        else:
            self.frame = tk.Frame(self.canvas, bg='#2a5565', relief=tk.RAISED, bd=3, highlightbackground='white', highlightthickness=2)
            title_text = f"클라이언트: {self.client_id}"
            title_color = 'white'
        
        self.canvas.create_window(self.x_pos, self.y_pos, window=self.frame, anchor="nw")
        
        # 제목
        title_label = tk.Label(self.frame, text=title_text, 
                              font=('Malgun Gothic', 14, 'bold'), bg='#2a5565', fg=title_color)
        title_label.pack(pady=(5, 10))
        
        # 스크롤 가능한 프레임
        canvas_frame = tk.Frame(self.frame, bg='#2a5565')
        canvas_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # 스크롤바가 있는 캔버스
        self.scroll_canvas = tk.Canvas(canvas_frame, width=500, height=318, bg='#2a5565')
        scrollbar = tk.Scrollbar(canvas_frame, orient="vertical", command=self.scroll_canvas.yview)
        self.scrollable_frame = tk.Frame(self.scroll_canvas, bg='#2a5565')
        
        self.scrollable_frame.bind(
            "<Configure>",
            lambda e: self.scroll_canvas.configure(scrollregion=self.scroll_canvas.bbox("all"))
        )
        
        self.scroll_canvas.create_window((0, 0), window=self.scrollable_frame, anchor="nw")
        self.scroll_canvas.configure(yscrollcommand=scrollbar.set)
        
        # 설정 항목들 생성
        self.create_setting_widgets()
        
        # 캔버스와 스크롤바 배치
        self.scroll_canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")
    
    def create_setting_widgets(self):
        """설정 위젯들 생성"""
        self.widgets = {}
        
        # 기본 설정
        basic_frame = tk.LabelFrame(self.scrollable_frame, text="기본 설정", 
                                   font=('Malgun Gothic', 10, 'bold'), bg='#2a5565', fg='white')
        basic_frame.pack(fill=tk.X, pady=2, padx=5)
        
        # 이름
        tk.Label(basic_frame, text="이름(예시: 궤도):", font=('Malgun Gothic', 9), bg='#2a5565', fg='white').pack(anchor=tk.W, padx=5, pady=1)
        self.widgets['name'] = tk.Entry(basic_frame, font=('Malgun Gothic', 9), width=20)
        self.widgets['name'].pack(anchor=tk.W, padx=5, pady=1)
        
        # 배출 바이패스 여부
        self.widgets['inspection_only'] = tk.BooleanVar()
        tk.Checkbutton(basic_frame, text="배출 바이패스 여부", variable=self.widgets['inspection_only'],
                      font=('Malgun Gothic', 9), bg='#2a5565', fg='white', selectcolor='#2a5565').pack(anchor=tk.W, padx=5, pady=1)
        
        # 검사 프레임 수
        tk.Label(basic_frame, text="검사 프레임 수:", font=('Malgun Gothic', 9), bg='#2a5565', fg='white').pack(anchor=tk.W, padx=5, pady=1)
        self.widgets['inspection_frame'] = tk.Entry(basic_frame, font=('Malgun Gothic', 9), width=8)
        self.widgets['inspection_frame'].pack(anchor=tk.W, padx=5, pady=1)
        
        # 이미지 저장 설정
        image_frame = tk.LabelFrame(self.scrollable_frame, text="이미지 저장 설정", 
                                   font=('Malgun Gothic', 10, 'bold'), bg='#2a5565', fg='white')
        image_frame.pack(fill=tk.X, pady=2, padx=5)
        
        # 원본 이미지 저장 여부
        self.widgets['origin_image_capture'] = tk.BooleanVar()
        tk.Checkbutton(image_frame, text="원본 이미지 저장 여부", variable=self.widgets['origin_image_capture'],
                      font=('Malgun Gothic', 9), bg='#2a5565', fg='white', selectcolor='#2a5565').pack(anchor=tk.W, padx=5, pady=1)
        
        # 불량 이미지 저장 여부
        self.widgets['ng_image_capture'] = tk.BooleanVar()
        tk.Checkbutton(image_frame, text="불량 이미지 저장 여부", variable=self.widgets['ng_image_capture'],
                      font=('Malgun Gothic', 9), bg='#2a5565', fg='white', selectcolor='#2a5565').pack(anchor=tk.W, padx=5, pady=1)
        
        # 검사 이미지 저장 여부
        self.widgets['inspection_image_capture'] = tk.BooleanVar()
        tk.Checkbutton(image_frame, text="검사 이미지 저장 여부", variable=self.widgets['inspection_image_capture'],
                      font=('Malgun Gothic', 9), bg='#2a5565', fg='white', selectcolor='#2a5565').pack(anchor=tk.W, padx=5, pady=1)
        
        # 불량별 설정
        label_frame = tk.LabelFrame(self.scrollable_frame, text="불량별 설정", 
                                   font=('Malgun Gothic', 10, 'bold'), bg='#2a5565', fg='white')
        label_frame.pack(fill=tk.X, pady=2, padx=5)
        
        # label_ng_conditions 입력 영역
        self.label_entries_frame = tk.Frame(label_frame, bg='#2a5565')
        self.label_entries_frame.pack(anchor=tk.W, padx=5, pady=1)
        
        # 중대 불량 리스트
        critical_frame = tk.LabelFrame(self.scrollable_frame, text="중대 불량 리스트", 
                                      font=('Malgun Gothic', 10, 'bold'), bg='#2a5565', fg='white')
        critical_frame.pack(fill=tk.X, pady=2, padx=5)
        
        # 중대 불량 체크박스들을 담을 프레임
        self.critical_checkboxes_frame = tk.Frame(critical_frame, bg='#2a5565')
        self.critical_checkboxes_frame.pack(anchor=tk.W, padx=5, pady=1)
        
        # 각인 검사 설정
        detection_frame = tk.LabelFrame(self.scrollable_frame, text="각인 검사 설정", 
                                        font=('Malgun Gothic', 10, 'bold'), bg='#2a5565', fg='white')
        detection_frame.pack(fill=tk.X, pady=2, padx=5)
        
        # 각인 검사 여부
        self.widgets['detection_use'] = tk.BooleanVar()
        tk.Checkbutton(detection_frame, text="각인 검사 여부", variable=self.widgets['detection_use'],
                      font=('Malgun Gothic', 9), bg='#2a5565', fg='white', selectcolor='#2a5565').pack(anchor=tk.W, padx=5, pady=1)
        
        # 각인 검사 프레임
        tk.Label(detection_frame, text="각인 검사 프레임(콤마(,)로 구분):", font=('Malgun Gothic', 9), bg='#2a5565', fg='white').pack(anchor=tk.W, padx=5, pady=1)
        self.widgets['detection_frame'] = tk.Entry(detection_frame, font=('Malgun Gothic', 9), width=25)
        self.widgets['detection_frame'].pack(anchor=tk.W, padx=5, pady=1)
        
        # 각인 양품 개수
        tk.Label(detection_frame, text="각인 양품 개수:", font=('Malgun Gothic', 9), bg='#2a5565', fg='white').pack(anchor=tk.W, padx=5, pady=1)
        self.widgets['ok_engrave'] = tk.Entry(detection_frame, font=('Malgun Gothic', 9), width=8)
        self.widgets['ok_engrave'].pack(anchor=tk.W, padx=5, pady=1)
        
        # 각인 검사 좌표
        tk.Label(detection_frame, text="각인 검사 좌표:", font=('Malgun Gothic', 9), bg='#2a5565', fg='white').pack(anchor=tk.W, padx=5, pady=1)
        detection_coord_frame = tk.Frame(detection_frame, bg='#2a5565')
        detection_coord_frame.pack(anchor=tk.W, padx=5, pady=1)
        
        tk.Label(detection_coord_frame, text="X:", font=('Malgun Gothic', 9), bg='#2a5565', fg='white').pack(side=tk.LEFT)
        self.widgets['detection_coords_x'] = tk.Entry(detection_coord_frame, font=('Malgun Gothic', 9), width=6)
        self.widgets['detection_coords_x'].pack(side=tk.LEFT, padx=2)
        
        tk.Label(detection_coord_frame, text="Y:", font=('Malgun Gothic', 9), bg='#2a5565', fg='white').pack(side=tk.LEFT)
        self.widgets['detection_coords_y'] = tk.Entry(detection_coord_frame, font=('Malgun Gothic', 9), width=6)
        self.widgets['detection_coords_y'].pack(side=tk.LEFT, padx=2)
        
        tk.Label(detection_coord_frame, text="W:", font=('Malgun Gothic', 9), bg='#2a5565', fg='white').pack(side=tk.LEFT)
        self.widgets['detection_coords_w'] = tk.Entry(detection_coord_frame, font=('Malgun Gothic', 9), width=6)
        self.widgets['detection_coords_w'].pack(side=tk.LEFT, padx=2)
        
        tk.Label(detection_coord_frame, text="H:", font=('Malgun Gothic', 9), bg='#2a5565', fg='white').pack(side=tk.LEFT)
        self.widgets['detection_coords_h'] = tk.Entry(detection_coord_frame, font=('Malgun Gothic', 9), width=6)
        self.widgets['detection_coords_h'].pack(side=tk.LEFT, padx=2)
        
        # 좌표 설정
        coord_frame = tk.LabelFrame(self.scrollable_frame, text="좌표 설정", 
                                   font=('Malgun Gothic', 10, 'bold'), bg='#2a5565', fg='white')
        coord_frame.pack(fill=tk.X, pady=2, padx=5)
        
        # 화면 출력 좌표
        tk.Label(coord_frame, text="화면 출력 좌표:", font=('Malgun Gothic', 9), bg='#2a5565', fg='white').pack(anchor=tk.W, padx=5, pady=1)
        show_coord_frame = tk.Frame(coord_frame, bg='#2a5565')
        show_coord_frame.pack(anchor=tk.W, padx=5, pady=1)
        
        tk.Label(show_coord_frame, text="X:", font=('Malgun Gothic', 9), bg='#2a5565', fg='white').pack(side=tk.LEFT)
        self.widgets['show_coord_x'] = tk.Entry(show_coord_frame, font=('Malgun Gothic', 9), width=6)
        self.widgets['show_coord_x'].pack(side=tk.LEFT, padx=2)
        
        tk.Label(show_coord_frame, text="Y:", font=('Malgun Gothic', 9), bg='#2a5565', fg='white').pack(side=tk.LEFT)
        self.widgets['show_coord_y'] = tk.Entry(show_coord_frame, font=('Malgun Gothic', 9), width=6)
        self.widgets['show_coord_y'].pack(side=tk.LEFT, padx=2)
        
        tk.Label(show_coord_frame, text="W:", font=('Malgun Gothic', 9), bg='#2a5565', fg='white').pack(side=tk.LEFT)
        self.widgets['show_coord_w'] = tk.Entry(show_coord_frame, font=('Malgun Gothic', 9), width=6)
        self.widgets['show_coord_w'].pack(side=tk.LEFT, padx=2)
        
        tk.Label(show_coord_frame, text="H:", font=('Malgun Gothic', 9), bg='#2a5565', fg='white').pack(side=tk.LEFT)
        self.widgets['show_coord_h'] = tk.Entry(show_coord_frame, font=('Malgun Gothic', 9), width=6)
        self.widgets['show_coord_h'].pack(side=tk.LEFT, padx=2)
        
        # 분류 모델 검사 좌표
        tk.Label(coord_frame, text="분류 모델 검사 좌표(명칭, 서브마스킹 사용여부, x, y, w, h, 회전각도):", font=('Malgun Gothic', 9), bg='#2a5565', fg='white').pack(anchor=tk.W, padx=5, pady=1)
        
        # 분류 모델 검사 좌표 입력 영역
        self.inspection_coords_frame = tk.Frame(coord_frame, bg='#2a5565')
        self.inspection_coords_frame.pack(anchor=tk.W, padx=5, pady=1)
        
        # 분류 모델 검사 좌표 추가 버튼
        add_inspection_coord_button = tk.Button(coord_frame, text="검사 영역 추가", command=self.add_inspection_coord,
                                               font=('Malgun Gothic', 9), bg='#4CAF50', fg='white')
        add_inspection_coord_button.pack(anchor=tk.W, padx=5, pady=2)
    
    def load_current_settings(self):
        """현재 설정값들을 위젯에 로드"""
        # Boolean 값들
        for key in ['detection_use', 'inspection_only', 'origin_image_capture', 'ng_image_capture', 'inspection_image_capture']:
            if key in self.client_data:
                self.widgets[key].set(self.client_data[key])
        
        # 문자열 값들
        for key in ['name']:
            if key in self.client_data:
                self.widgets[key].insert(0, str(self.client_data[key]))
        
        # 디텍션 검사 프레임
        if 'detection_frame' in self.client_data:
            value = self.client_data['detection_frame']
            if isinstance(value, list):
                self.widgets['detection_frame'].insert(0, ','.join(map(str, value)))
            else:
                self.widgets['detection_frame'].insert(0, str(value))
        
        # 좌표 값들 (개별 필드로 분리)
        if 'show_coord' in self.client_data:
            coords = self.client_data['show_coord']
            if isinstance(coords, list) and len(coords) >= 4:
                self.widgets['show_coord_x'].insert(0, str(coords[0]))
                self.widgets['show_coord_y'].insert(0, str(coords[1]))
                self.widgets['show_coord_w'].insert(0, str(coords[2]))
                self.widgets['show_coord_h'].insert(0, str(coords[3]))
        
        if 'detection_coords' in self.client_data:
            coords = self.client_data['detection_coords']
            if isinstance(coords, list) and len(coords) >= 4:
                self.widgets['detection_coords_x'].insert(0, str(coords[0]))
                self.widgets['detection_coords_y'].insert(0, str(coords[1]))
                self.widgets['detection_coords_w'].insert(0, str(coords[2]))
                self.widgets['detection_coords_h'].insert(0, str(coords[3]))
        
        # 분류 모델 검사 좌표
        if 'inspection_coords' in self.client_data:
            self.load_inspection_coords()
        
        # 정수 값들
        for key in ['ok_engrave', 'inspection_frame']:
            if key in self.client_data:
                self.widgets[key].insert(0, str(self.client_data[key]))
        
        # 중대 불량 리스트와 label_ng_conditions 로드
        self.load_critical_ng_list()
        self.load_label_ng_conditions()
    
    def load_inspection_coords(self):
        """분류 모델 검사 좌표 로드"""
        # 기존 입력 필드들 제거
        for widget in self.inspection_coords_frame.winfo_children():
            widget.destroy()
        
        if 'inspection_coords' in self.client_data:
            for area_name, coords in self.client_data['inspection_coords'].items():
                self.create_inspection_coord_entry(area_name, coords)
    
    def create_inspection_coord_entry(self, area_name, coords=None):
        """분류 모델 검사 좌표 입력 필드 생성"""
        if coords is None:
            coords = ["", 0, 0, 100, 100, 0]
        
        row_frame = tk.Frame(self.inspection_coords_frame, bg='#2a5565')
        row_frame.pack(anchor=tk.W, pady=2)
        
        entry_id = f"coord_{uuid.uuid4().hex}"  # 고유 ID 생성 (UUID 기반)
        
        # 검사 영역 이름
        tk.Label(row_frame, text="영역명:", font=('Malgun Gothic', 8), bg='#2a5565', fg='white').pack(side=tk.LEFT)
        name_entry = tk.Entry(row_frame, font=('Malgun Gothic', 8), width=8)
        name_entry.insert(0, area_name)
        name_entry.pack(side=tk.LEFT, padx=2)
        
        # sub 마스킹 사용 여부
        sub_var = tk.BooleanVar()
        sub_var.set(coords[0] == "_sub" if len(coords) > 0 else False)
        sub_check = tk.Checkbutton(row_frame, text="sub", variable=sub_var, 
                                  font=('Malgun Gothic', 8), bg='#2a5565', fg='white', selectcolor='#2a5565')
        sub_check.pack(side=tk.LEFT, padx=2)
        
        # X 좌표
        tk.Label(row_frame, text="X:", font=('Malgun Gothic', 8), bg='#2a5565', fg='white').pack(side=tk.LEFT)
        x_entry = tk.Entry(row_frame, font=('Malgun Gothic', 8), width=5)
        x_entry.insert(0, str(coords[1]) if len(coords) > 1 else '0')
        x_entry.pack(side=tk.LEFT, padx=2)
        
        # Y 좌표
        tk.Label(row_frame, text="Y:", font=('Malgun Gothic', 8), bg='#2a5565', fg='white').pack(side=tk.LEFT)
        y_entry = tk.Entry(row_frame, font=('Malgun Gothic', 8), width=5)
        y_entry.insert(0, str(coords[2]) if len(coords) > 2 else '0')
        y_entry.pack(side=tk.LEFT, padx=2)
        
        # W 좌표
        tk.Label(row_frame, text="W:", font=('Malgun Gothic', 8), bg='#2a5565', fg='white').pack(side=tk.LEFT)
        w_entry = tk.Entry(row_frame, font=('Malgun Gothic', 8), width=5)
        w_entry.insert(0, str(coords[3]) if len(coords) > 3 else '100')
        w_entry.pack(side=tk.LEFT, padx=2)
        
        # H 좌표
        tk.Label(row_frame, text="H:", font=('Malgun Gothic', 8), bg='#2a5565', fg='white').pack(side=tk.LEFT)
        h_entry = tk.Entry(row_frame, font=('Malgun Gothic', 8), width=5)
        h_entry.insert(0, str(coords[4]) if len(coords) > 4 else '100')
        h_entry.pack(side=tk.LEFT, padx=2)
        
        # 각도
        tk.Label(row_frame, text="각도:", font=('Malgun Gothic', 8), bg='#2a5565', fg='white').pack(side=tk.LEFT)
        angle_entry = tk.Entry(row_frame, font=('Malgun Gothic', 8), width=5)
        angle_entry.insert(0, str(coords[5]) if len(coords) > 5 else '0')
        angle_entry.pack(side=tk.LEFT, padx=2)
        
        # 삭제 버튼
        delete_button = tk.Button(row_frame, text="삭제", command=lambda: self.delete_inspection_coord(entry_id, row_frame),
                                 font=('Malgun Gothic', 8), bg='#f44336', fg='white')
        delete_button.pack(side=tk.LEFT, padx=5)
        
        # 위젯들을 저장 (고유한 키로 저장)
        self.widgets[f'{entry_id}_name'] = name_entry
        self.widgets[f'{entry_id}_sub'] = sub_var
        self.widgets[f'{entry_id}_x'] = x_entry
        self.widgets[f'{entry_id}_y'] = y_entry
        self.widgets[f'{entry_id}_w'] = w_entry
        self.widgets[f'{entry_id}_h'] = h_entry
        self.widgets[f'{entry_id}_angle'] = angle_entry
    
    def add_inspection_coord(self):
        """새 분류 모델 검사 좌표 입력 필드 추가"""
        self.create_inspection_coord_entry("새영역")
    
    def delete_inspection_coord(self, entry_id, frame):
        """분류 모델 검사 좌표 입력 필드 삭제"""
        # 해당 entry_id의 위젯들을 self.widgets에서 제거
        keys_to_remove = []
        for key in self.widgets.keys():
            if key.startswith(entry_id):
                keys_to_remove.append(key)
        
        # 키들 제거
        for key in keys_to_remove:
            del self.widgets[key]
        
        # 프레임 제거
        frame.destroy()
    
    def load_critical_ng_list(self):
        """중대 불량 리스트 로드"""
        # 기존 체크박스들 제거
        for widget in self.critical_checkboxes_frame.winfo_children():
            widget.destroy()
        
        # label_ng_conditions에서 라벨들을 가져와서 체크박스 생성
        if 'label_ng_conditions' in self.client_data:
            labels = list(self.client_data['label_ng_conditions'].keys())
            labels = labels + ['DETECTION']  # 각인 검사 불량 추가
            critical_list = self.client_data.get('critical_ng_list', [])
            
            for label in labels:
                var = tk.BooleanVar()
                var.set(label in critical_list)
                self.widgets[f'critical_{label}'] = var
                
                checkbox = tk.Checkbutton(self.critical_checkboxes_frame, text=label, variable=var,
                                         font=('Malgun Gothic', 9), bg='#2a5565', fg='white', selectcolor='#2a5565')
                checkbox.pack(anchor=tk.W, padx=5, pady=1)
    
    def load_label_ng_conditions(self):
        """label_ng_conditions 로드"""
        # 기존 입력 필드들 제거
        for widget in self.label_entries_frame.winfo_children():
            widget.destroy()
        
        if 'label_ng_conditions' in self.client_data:
            for label, conditions in self.client_data['label_ng_conditions'].items():
                self.create_label_entry(label, conditions)
    
    def create_label_entry(self, label, conditions=None):
        """라벨 입력 필드 생성"""
        if conditions is None:
            conditions = ['미지정', 90, 2, 3]
        
        label_frame = tk.Frame(self.label_entries_frame, bg='#2a5565')
        label_frame.pack(anchor=tk.W, padx=5, pady=2)
        
        # 라벨명
        tk.Label(label_frame, text=f"라벨: {label}", font=('Malgun Gothic', 9), bg='#2a5565', fg='white').pack(anchor=tk.W)
        
        # 입력 필드들
        input_frame = tk.Frame(label_frame, bg='#2a5565')
        input_frame.pack(anchor=tk.W, padx=10, pady=1)
        
        # 불량명
        tk.Label(input_frame, text="불량명:", font=('Malgun Gothic', 8), bg='#2a5565', fg='white').pack(side=tk.LEFT)
        name_entry = tk.Entry(input_frame, font=('Malgun Gothic', 8), width=10)
        name_entry.insert(0, str(conditions[0]) if len(conditions) > 0 else '미지정')
        name_entry.pack(side=tk.LEFT, padx=2)
        
        # 검출 제한 수치
        tk.Label(input_frame, text="제한 수치:", font=('Malgun Gothic', 8), bg='#2a5565', fg='white').pack(side=tk.LEFT)
        limit_entry = tk.Entry(input_frame, font=('Malgun Gothic', 8), width=6)
        limit_entry.insert(0, str(conditions[1]) if len(conditions) > 1 else '90')
        limit_entry.pack(side=tk.LEFT, padx=2)
        
        # 연속 발생
        tk.Label(input_frame, text="연속 제한:", font=('Malgun Gothic', 8), bg='#2a5565', fg='white').pack(side=tk.LEFT)
        consecutive_entry = tk.Entry(input_frame, font=('Malgun Gothic', 8), width=6)
        consecutive_entry.insert(0, str(conditions[2]) if len(conditions) > 2 else '2')
        consecutive_entry.pack(side=tk.LEFT, padx=2)
        
        # 종합 발생
        tk.Label(input_frame, text="종합 제한:", font=('Malgun Gothic', 8), bg='#2a5565', fg='white').pack(side=tk.LEFT)
        total_entry = tk.Entry(input_frame, font=('Malgun Gothic', 8), width=6)
        total_entry.insert(0, str(conditions[3]) if len(conditions) > 3 else '3')
        total_entry.pack(side=tk.LEFT, padx=2)
        
        # 위젯들을 저장
        self.widgets[f'label_{label}_name'] = name_entry
        self.widgets[f'label_{label}_limit'] = limit_entry
        self.widgets[f'label_{label}_consecutive'] = consecutive_entry
        self.widgets[f'label_{label}_total'] = total_entry
    
    def save_settings(self):
        """설정값들을 저장"""
        try:
            # Boolean 값들 저장 (검증 없이)
            for key in ['detection_use', 'inspection_only', 'origin_image_capture', 'ng_image_capture', 'inspection_image_capture']:
                self.client_data[key] = self.widgets[key].get()
            
            # 1. 이름 검증
            name_value = self.widgets['name'].get().strip()
            if not name_value:
                messagebox.showerror("오류", f"{self.client_id}의 클라이언트 이름을 입력해주세요.")
                return False
            self.client_data['name'] = name_value
            
            # 2. 검사 프레임 수 검증
            try:
                inspection_frame_value = int(self.widgets['inspection_frame'].get())
                if inspection_frame_value <= 0:
                    messagebox.showerror("오류", f"{self.client_id}의 검사 프레임 수는 1 이상이어야 합니다.")
                    return False
                self.client_data['inspection_frame'] = inspection_frame_value
            except ValueError:
                messagebox.showerror("오류", f"{self.client_id}의 검사 프레임 수는 숫자로 입력해주세요.")
                return False
            
            # 3. 불량별 설정 검증 (이름, 정수 3칸)
            if not self.validate_label_ng_conditions():
                return False
            
            # 4. 각인 검사 프레임 검증
            if self.widgets['detection_use'].get():
                try:
                    value = self.widgets['detection_frame'].get().strip()
                    if not value:
                        messagebox.showerror("오류", f"{self.client_id}의 각인 검사 프레임을 입력해주세요.")
                        return False
                    # 쉼표로 구분된 문자열을 리스트로 변환
                    frame_list = [int(x.strip()) for x in value.split(',')]
                    if not frame_list or any(f <= 0 for f in frame_list):
                        messagebox.showerror("오류", f"{self.client_id}의 각인 검사 프레임은 1 이상의 숫자여야 합니다.")
                        return False
                    self.client_data['detection_frame'] = frame_list
                except ValueError:
                    messagebox.showerror("오류", f"{self.client_id}의 각인 검사 프레임 값이 올바르지 않습니다. (예: 5,10,15)")
                    return False
            else:
                # 각인 검사가 비활성화된 경우 빈 리스트로 설정
                self.client_data['detection_frame'] = []
            
            # 5. 각인 양품 개수 검증
            try:
                ok_engrave_value = int(self.widgets['ok_engrave'].get())
                if ok_engrave_value < 0:
                    messagebox.showerror("오류", f"{self.client_id}의 각인 양품 개수는 0 이상이어야 합니다.")
                    return False
                self.client_data['ok_engrave'] = ok_engrave_value
            except ValueError:
                messagebox.showerror("오류", f"{self.client_id}의 각인 양품 개수는 숫자로 입력해주세요.")
                return False
            
            # 6. 각인 검사 좌표 검증
            detection_coords_raw = [
                self.widgets['detection_coords_x'].get().strip(),
                self.widgets['detection_coords_y'].get().strip(),
                self.widgets['detection_coords_w'].get().strip(),
                self.widgets['detection_coords_h'].get().strip()
            ]
            if self.widgets['detection_use'].get():
                if not self.validate_coord_list(detection_coords_raw, f"{self.client_id}의 각인 검사"):
                    return False
                detection_coords = [int(x) for x in detection_coords_raw]
            else:
                detection_coords = [int(x) if x else 0 for x in detection_coords_raw]
            self.client_data['detection_coords'] = detection_coords
            
            # 7. 화면 출력 좌표 검증
            show_coords_raw = [
                self.widgets['show_coord_x'].get().strip(),
                self.widgets['show_coord_y'].get().strip(),
                self.widgets['show_coord_w'].get().strip(),
                self.widgets['show_coord_h'].get().strip()
            ]
            if not self.validate_coord_list(show_coords_raw, f"{self.client_id}의 화면 출력"):
                return False
            show_coords = [int(x) for x in show_coords_raw]
            self.client_data['show_coord'] = show_coords
            
            # 8. 분류 모델 검사 좌표 검증 (영역명, 4개좌표, 각도)
            if not self.validate_inspection_coords():
                return False
            
            # 검증 완료 후 저장 함수들 호출
            self.save_label_ng_conditions()
            if not self.save_inspection_coords():
                return False  # 중복 확인에서 취소된 경우
            
            # 중대 불량 리스트 저장
            self.save_critical_ng_list()
            
            print(f"[SAVE] Client {self.client_id} settings updated successfully")
            return True
            
        except Exception as e:
            messagebox.showerror("오류", f"저장 중 오류가 발생했습니다: {str(e)}")
            raise e  # 상위 메서드에서 처리할 수 있도록 예외를 다시 발생시킴
    
    def save_critical_ng_list(self):
        """중대 불량 리스트 저장"""
        critical_list = []
        for key, var in self.widgets.items():
            if key.startswith('critical_') and isinstance(var, tk.BooleanVar):
                if var.get():
                    label = key.replace('critical_', '')
                    critical_list.append(label)
        
        self.client_data['critical_ng_list'] = critical_list
    
    def save_label_ng_conditions(self):
        """label_ng_conditions 저장"""
        label_conditions = {}
        
        # 기존 label_ng_conditions에서 라벨들을 가져와서 저장
        if 'label_ng_conditions' in self.client_data:
            for label in self.client_data['label_ng_conditions'].keys():
                if f'label_{label}_name' in self.widgets:
                    try:
                        name = self.widgets[f'label_{label}_name'].get()
                        limit = int(self.widgets[f'label_{label}_limit'].get())
                        consecutive = int(self.widgets[f'label_{label}_consecutive'].get())
                        total = int(self.widgets[f'label_{label}_total'].get())
                        
                        label_conditions[label] = [name, limit, consecutive, total]
                    except:
                        messagebox.showerror("오류", f"라벨 {label}의 설정값이 올바르지 않습니다.")
                        return
        
        self.client_data['label_ng_conditions'] = label_conditions

    def destroy(self):
        """프레임 제거"""
        self.frame.destroy()

    def save_inspection_coords(self):
        """분류 모델 검사 좌표 저장"""
        inspection_coords = {}
        
        # 위젯에서 coord로 시작하는 키들을 찾아서 처리
        coord_entries = {}
        
        for key, widget in self.widgets.items():
            if key.startswith('coord_'):
                # coord_숫자_필드명 형태에서 숫자와 필드명 추출
                parts = key.split('_')
                if len(parts) >= 3:
                    try:
                        entry_id = f"{parts[0]}_{parts[1]}"  # coord_숫자
                        field_name = '_'.join(parts[2:])  # 나머지 부분이 필드명
                        
                        if entry_id not in coord_entries:
                            coord_entries[entry_id] = {}
                        coord_entries[entry_id][field_name] = widget
                    except ValueError:
                        # 숫자가 아닌 경우 건너뛰기
                        continue
               
        # 중복된 영역명 확인
        area_names = []
        for entry_id, fields in coord_entries.items():
            try:
                required_fields = ['name', 'sub', 'x', 'y', 'w', 'h', 'angle']
                if not all(field in fields for field in required_fields):
                    continue
                
                area_name = fields['name'].get()
                if area_name:  # 영역명이 비어있지 않으면 추가
                    area_names.append(area_name)
            except (ValueError, KeyError):
                continue
        
        # 중복된 영역명이 있는지 확인
        duplicate_names = [name for name in set(area_names) if area_names.count(name) > 1]
        if duplicate_names:
            duplicate_list = ", ".join(duplicate_names)
            result = messagebox.askyesno("중복 확인", 
                                       f"다음 영역명이 중복됩니다:\n{duplicate_list}\n\n"
                                       f"중복된 영역명은 자동으로 하나만 저장됩니다.\n"
                                       f"계속 진행하시겠습니까?")
            if not result:
                return False
        
        # 각 좌표 엔트리를 딕셔너리로 변환
        for entry_id, fields in coord_entries.items():
            try:
                # 필수 필드들이 모두 있는지 확인
                required_fields = ['name', 'sub', 'x', 'y', 'w', 'h', 'angle']
                if not all(field in fields for field in required_fields):
                    continue
                
                area_name = fields['name'].get()
                if not area_name:  # 영역명이 비어있으면 건너뛰기
                    continue
                
                sub_used = fields['sub'].get()
                x = int(fields['x'].get())
                y = int(fields['y'].get())
                w = int(fields['w'].get())
                h = int(fields['h'].get())
                angle = int(fields['angle'].get())
                
                # sub 마스킹 사용 여부에 따라 첫 번째 값 설정
                first_value = "_sub" if sub_used else ""
                
                inspection_coords[area_name] = [first_value, x, y, w, h, angle]
                
            except ValueError:
                messagebox.showerror("오류", f"분류 모델 검사 좌표 값이 올바르지 않습니다.")
                return False
            except KeyError as e:
                continue
        
        self.client_data['inspection_coords'] = inspection_coords
        return True

    def get_settings(self):
        """현재 위젯의 설정값들을 딕셔너리로 반환 (JSON 형식과 동일하게)"""
        settings = {}
        
        # Boolean 값들
        for key in ['detection_use', 'inspection_only', 'origin_image_capture', 'ng_image_capture', 'inspection_image_capture']:
            settings[key] = self.widgets[key].get()
        
        # 문자열 값들
        for key in ['name']:
            settings[key] = self.widgets[key].get()
        
        # 디텍션 검사 프레임 (문자열을 리스트로 변환)
        detection_frame_str = self.widgets['detection_frame'].get().strip()
        if detection_frame_str:
            try:
                settings['detection_frame'] = [int(x.strip()) for x in detection_frame_str.split(',')]
            except ValueError:
                settings['detection_frame'] = []
        else:
            settings['detection_frame'] = []
        
        # 좌표 값들 (문자열을 정수로 변환)
        show_coords = [
            int(self.widgets['show_coord_x'].get()) if self.widgets['show_coord_x'].get() else 0,
            int(self.widgets['show_coord_y'].get()) if self.widgets['show_coord_y'].get() else 0,
            int(self.widgets['show_coord_w'].get()) if self.widgets['show_coord_w'].get() else 0,
            int(self.widgets['show_coord_h'].get()) if self.widgets['show_coord_h'].get() else 0
        ]
        settings['show_coord'] = show_coords
        
        detection_coords = [
            int(self.widgets['detection_coords_x'].get()) if self.widgets['detection_coords_x'].get() else 0,
            int(self.widgets['detection_coords_y'].get()) if self.widgets['detection_coords_y'].get() else 0,
            int(self.widgets['detection_coords_w'].get()) if self.widgets['detection_coords_w'].get() else 0,
            int(self.widgets['detection_coords_h'].get()) if self.widgets['detection_coords_h'].get() else 0
        ]
        settings['detection_coords'] = detection_coords
        
        # 분류 모델 검사 좌표 (문자열을 정수로 변환)
        inspection_coords = {}
        coord_entries = {}
        
        for key, widget in self.widgets.items():
            if key.startswith('coord_'):
                parts = key.split('_')
                if len(parts) >= 3:
                    try:
                        entry_id = f"{parts[0]}_{parts[1]}"
                        field_name = '_'.join(parts[2:])
                        
                        if entry_id not in coord_entries:
                            coord_entries[entry_id] = {}
                        coord_entries[entry_id][field_name] = widget
                    except ValueError:
                        continue
               
        for entry_id, fields in coord_entries.items():
            try:
                required_fields = ['name', 'sub', 'x', 'y', 'w', 'h', 'angle']
                if not all(field in fields for field in required_fields):
                    continue
                
                area_name = fields['name'].get()
                if not area_name:
                    continue
                
                sub_used = fields['sub'].get()
                x = int(fields['x'].get()) if fields['x'].get() else 0
                y = int(fields['y'].get()) if fields['y'].get() else 0
                w = int(fields['w'].get()) if fields['w'].get() else 0
                h = int(fields['h'].get()) if fields['h'].get() else 0
                angle = int(fields['angle'].get()) if fields['angle'].get() else 0
                
                first_value = "_sub" if sub_used else ""
                inspection_coords[area_name] = [first_value, x, y, w, h, angle]
                
            except (ValueError, KeyError):
                continue
        
        settings['inspection_coords'] = inspection_coords
        
        # 정수 값들 (문자열을 정수로 변환)
        for key in ['ok_engrave', 'inspection_frame']:
            try:
                settings[key] = int(self.widgets[key].get()) if self.widgets[key].get() else 0
            except ValueError:
                settings[key] = 0
        
        # 중대 불량 리스트
        critical_list = []
        for key, var in self.widgets.items():
            if key.startswith('critical_') and isinstance(var, tk.BooleanVar):
                if var.get():
                    label = key.replace('critical_', '')
                    critical_list.append(label)
        settings['critical_ng_list'] = critical_list
        
        # label_ng_conditions (문자열을 정수로 변환)
        label_conditions = {}
        if 'label_ng_conditions' in self.client_data:
            for label in self.client_data['label_ng_conditions'].keys():
                if f'label_{label}_name' in self.widgets:
                    try:
                        name = self.widgets[f'label_{label}_name'].get()
                        limit = int(self.widgets[f'label_{label}_limit'].get()) if self.widgets[f'label_{label}_limit'].get() else 0
                        consecutive = int(self.widgets[f'label_{label}_consecutive'].get()) if self.widgets[f'label_{label}_consecutive'].get() else 0
                        total = int(self.widgets[f'label_{label}_total'].get()) if self.widgets[f'label_{label}_total'].get() else 0
                        
                        label_conditions[label] = [name, limit, consecutive, total]
                    except ValueError:
                        continue
        settings['label_ng_conditions'] = label_conditions
        
        return settings
    
    def get_inspection_coords_from_widgets(self):
        """위젯에서 분류 모델 검사 좌표를 가져오기"""
        inspection_coords = {}
        
        # 위젯에서 coord로 시작하는 키들을 찾아서 처리
        coord_entries = {}
        
        for key, widget in self.widgets.items():
            if key.startswith('coord_'):
                # coord_숫자_필드명 형태에서 숫자와 필드명 추출
                parts = key.split('_')
                if len(parts) >= 3:
                    try:
                        entry_id = f"{parts[0]}_{parts[1]}"  # coord_숫자
                        field_name = '_'.join(parts[2:])  # 나머지 부분이 필드명
                        
                        if entry_id not in coord_entries:
                            coord_entries[entry_id] = {}
                        coord_entries[entry_id][field_name] = widget
                    except ValueError:
                        # 숫자가 아닌 경우 건너뛰기
                        continue
               
        # 각 좌표 엔트리를 딕셔너리로 변환
        for entry_id, fields in coord_entries.items():
            try:
                # 필수 필드들이 모두 있는지 확인
                required_fields = ['name', 'sub', 'x', 'y', 'w', 'h', 'angle']
                if not all(field in fields for field in required_fields):
                    continue
                
                area_name = fields['name'].get()
                if not area_name:  # 영역명이 비어있으면 건너뛰기
                    continue
                
                sub_used = fields['sub'].get()
                x = fields['x'].get()
                y = fields['y'].get()
                w = fields['w'].get()
                h = fields['h'].get()
                angle = fields['angle'].get()
                
                # sub 마스킹 사용 여부에 따라 첫 번째 값 설정
                first_value = "_sub" if sub_used else ""
                
                inspection_coords[area_name] = [first_value, x, y, w, h, angle]
                
            except KeyError as e:
                continue
        
        return inspection_coords

    def validate_label_ng_conditions(self):
        """불량별 설정 검증 (이름, 정수 3칸)"""
        if 'label_ng_conditions' not in self.client_data:
            return True
            
        for label in self.client_data['label_ng_conditions'].keys():
            if f'label_{label}_name' in self.widgets:
                try:
                    # 이름 검증
                    name = self.widgets[f'label_{label}_name'].get().strip()
                    if not name:
                        messagebox.showerror("오류", f"{self.client_id}의 {label}라벨의 이름을 입력해주세요.")
                        return False
                    
                    # 정수 3칸 검증
                    limit = int(self.widgets[f'label_{label}_limit'].get())
                    consecutive = int(self.widgets[f'label_{label}_consecutive'].get())
                    total = int(self.widgets[f'label_{label}_total'].get())
                    
                    # limit 값 검증
                    if limit < 0 or limit > 100:
                        messagebox.showerror("오류", f"{self.client_id}의 라벨 {label} 제한 수치는 0~100 사이여야 합니다.")
                        return False
                    
                    if consecutive < 0 or total < 0:
                        messagebox.showerror("오류", f"{self.client_id}의 라벨 {label} 설정값은 0 이상이어야 합니다.")
                        return False
                        
                except ValueError:
                    messagebox.showerror("오류", f"{self.client_id}의 라벨 {label} 설정값은 숫자로 입력해주세요.")
                    return False
        return True

    def validate_inspection_coords(self):
        """분류 모델 검사 좌표 검증 (영역명, 4개좌표, 각도)"""
        coord_entries = {}
        
        # 위젯에서 coord로 시작하는 키들을 찾아서 처리
        for key, widget in self.widgets.items():
            if key.startswith('coord_'):
                parts = key.split('_')
                if len(parts) >= 3:
                    try:
                        entry_id = f"{parts[0]}_{parts[1]}"  # coord_숫자
                        field_name = '_'.join(parts[2:])  # 나머지 부분이 필드명
                        
                        if entry_id not in coord_entries:
                            coord_entries[entry_id] = {}
                        coord_entries[entry_id][field_name] = widget
                    except ValueError:
                        continue
               
        # 각 좌표 엔트리 검증
        for entry_id, fields in coord_entries.items():
            try:
                # 필수 필드들이 모두 있는지 확인
                required_fields = ['name', 'sub', 'x', 'y', 'w', 'h', 'angle']
                if not all(field in fields for field in required_fields):
                    continue
                
                # 영역명 검증
                area_name = fields['name'].get().strip()
                if not area_name:
                    messagebox.showerror("오류", f"{self.client_id}의 분류 모델 검사 좌표에 영역명을 입력해주세요.")
                    return False
                
                # 4개 좌표 검증 (반복성 있게)
                coord_raw = [fields['x'].get().strip(), fields['y'].get().strip(), fields['w'].get().strip(), fields['h'].get().strip()]
                if not self.validate_coord_list(coord_raw, f"{self.client_id}의 분류 모델 검사 좌표 {area_name}"):
                    return False
                x, y, w, h = [int(val) for val in coord_raw]
                
                # 각도 검증
                angle_raw = [fields['angle'].get().strip()]
                if not self.validate_coord_list(angle_raw, f"{self.client_id}의 분류 모델 검사 좌표 {area_name}"):
                    return False
                angle = int(angle_raw[0])
                if angle > 360:
                    messagebox.showerror("오류", f"{self.client_id}의 분류 모델 검사 좌표 {area_name}의 각도는 0~360 사이여야 합니다.")
                    return False
                
            except ValueError:
                messagebox.showerror("오류", f"{self.client_id}의 분류 모델 검사 좌표 {area_name}의 값이 올바르지 않습니다.")
                return False
            except KeyError:
                continue
        return True
    def validate_coord_list(self, coord_list, label):
        for val in coord_list:
            if val == "" or val is None:
                messagebox.showerror("오류", f"{label} 좌표에 빈 값이 있습니다.")
                return False
            try:
                num = int(val)
            except ValueError:
                messagebox.showerror("오류", f"{label} 좌표에 숫자가 아닌 값이 있습니다.")
                return False
            if num < 0:
                messagebox.showerror("오류", f"{label} 좌표에 음수가 있습니다.")
                return False
        return True


# ▶ 최근 불량 확인
class RecentNgCheckFrame(tk.Frame):
    def __init__(self, master=None):
        super().__init__(master)
        self.master = master
        # bg 3단계로 구성 1.클라이언트 선택, 2.검사 영역 선택, 3.이미지 확인
        self.first_bg = ImageTk.PhotoImage(file=f"bg/{line_type}/recent_ng_check_bg.png")
        self.second_bg = ImageTk.PhotoImage(file=f"bg/common/select_check_part_bg.png")
        self.third_bg = ImageTk.PhotoImage(file=f"bg/common/recent_image_check_bg.png")
        
        self.client_blink_image = ImageTk.PhotoImage(file=f"bg/{line_type}/recent_ng_check_blink.png")

        self.color_palette = [
            (255, 99, 71),    # Tomato
            (255, 165, 0),    # Orange
            (255, 215, 0),    # Gold
            (50, 205, 50),    # Lime Green
            (0, 191, 255),    # Deep Sky Blue
            (30, 144, 255),   # Dodger Blue
            (138, 43, 226),   # Blue Violet
            (255, 20, 147),   # Deep Pink
            (0, 255, 255),    # Cyan
            (255, 105, 180),  # Hot Pink
        ]

        self.state = 'first'  # first, second, third // first: 클라이언트 선택, second: 검사 영역 선택, third: 이미지 확인
        self.selected_client_id = None
        self.selected_area_name = None

        self.show_origin_image = None

        self.ok_images = []
        self.ng_images = []
        self.ok_index = 0
        self.ng_index = 0

        self.click_coord_map = {}
        for i in range(client_num):
            if i < 3:
                self.click_coord_map[f"{line_config['client_ids'][i]}"] = [96+(i*441), 140, 400, 300]
            else:
                self.click_coord_map[f"{line_config['client_ids'][i]}"] = [96+((i-3)*441), 553, 400, 300]
        
        # 깜빡임 스레드 제어를 위한 변수
        self.blink_thread = None
        self.blink_running = False

        self.create_widgets()
        
    def create_widgets(self):
        self.grid(row=0, column=0)
        self.recent_canvas = tk.Canvas(self, width=1920, height=1080)
        self.BG = self.recent_canvas.create_image(0, 0, image=self.first_bg, anchor="nw")

        # first 클라이언트 영역 깜빡임 위치
        self.blink_place = self.recent_canvas.create_image(84, 128, image=self.client_blink_image, anchor="nw", state="hidden")

        # second 원본 이미지 표시 위치
        self.origin_image_place = self.recent_canvas.create_image(552, 224, anchor="nw", state="hidden")  

        # third 검사 영역 표시 위치
        self.ok_image_place = self.recent_canvas.create_image(210, 278, anchor="nw", state="hidden")  # 양품 이미지
        self.ng_image_place = self.recent_canvas.create_image(1115, 278, anchor="nw", state="hidden")  # 불량 이미지

        self.recent_canvas.bind("<Button-1>", self.main_btn)
        self.recent_canvas.pack()
    
    def tkraise(self):
        super().tkraise()
        self.state = 'first'
        self.clear_screen()
        self.recent_canvas.itemconfig(self.BG, image=self.first_bg)

        # 새로운 스레드 시작
        self.blink_running = True
        self.blink_thread = threading.Thread(target=self.blink_on, daemon=True)
        self.blink_thread.start()

    def main_btn(self, event):
        x = event.x
        y = event.y

        if 1870 < x < 1912 and 11 < y < 53:
            print("program exit")
            MF.on_closing()
        
        # 메인 화면 버튼 클릭
        elif 89 < x < 271 and 976 < y < 1051:
            print("main frame open")
            MF.tkraise()
        
        # 이력 조회 버튼 클릭
        elif 1189 < x < 1377 and 972 < y < 1055:
            print("history frame open")
            HF.tkraise()
        
        # 관리자 버튼 클릭
        elif 1477 < x < 1659 and 972 < y < 1055:
            print("admin frame open")
            AF.tkraise()

        # 최근 불량 확인 버튼 클릭
        elif 644 < x < 826 and 976 < y < 1051:
            print("recent ng check frame close")
            RN.tkraise()

        else:
            if self.state == 'first':
                for client_id, coord in self.click_coord_map.items():  # 클라이언트 영역 클릭
                    if coord[0] < x < coord[0] + coord[2] and coord[1] < y < coord[1] + coord[3]:
                        print(f"client {client_id} clicked")
                        self.selected_client_id = client_id
                        self.blink_off()
                        self.select_part()
                        break

            elif self.state == 'second':
                # 이미지 내 상대 좌표
                rel_x = event.x - 552
                rel_y = event.y - 224
                if rel_x < 0 or rel_y < 0:  # 이미지 바깥 클릭
                    return  

                for area in self.clickable_areas:
                    x0, y0, x1, y1 = area['coords']
                    if x0 <= rel_x <= x1 and y0 <= rel_y <= y1:
                        print(f"Clicked area: {area['key']}")
                        self.selected_area_name = area['key']
                        self.select_area()
                        break

            elif self.state == 'third':
                if 128 < x < 188 and 546 < y < 606:  # OK ←
                    if self.ok_images and self.ok_index > 0:
                        self.ok_index -= 1
                        self.show_ok_image()
                elif 828 < x < 888 and 546 < y < 606:  # OK →
                    if self.ok_images and self.ok_index < len(self.ok_images) - 1:
                        self.ok_index += 1
                        self.show_ok_image()
                elif 1034 < x < 1094 and 546 < y < 606:  # NG ←
                    if self.ng_images and self.ng_index > 0:
                        self.ng_index -= 1
                        self.show_ng_image()
                elif 1734 < x < 1794 and 546 < y < 606:  # NG →
                    if self.ng_images and self.ng_index < len(self.ng_images) - 1:
                        self.ng_index += 1
                        self.show_ng_image()

    def blink_on(self):
        """클라이언트 영역 깜빡임 시작"""
        while self.blink_running:
            # UI 업데이트는 메인 스레드에서 실행
            self.master.after(0, lambda: self.recent_canvas.itemconfig(self.blink_place, state="normal"))
            time.sleep(0.5)
            if not self.blink_running:
                break
            
            self.master.after(0, lambda: self.recent_canvas.itemconfig(self.blink_place, state="hidden"))
            time.sleep(0.5)
            if not self.blink_running:
                break

    def blink_off(self):
        """클라이언트 영역 깜빡임 종료"""
        self.blink_running = False
        self.recent_canvas.itemconfig(self.blink_place, state="hidden")
        # 스레드가 실행 중이라면 종료될 때까지 잠시 대기
        if self.blink_thread and self.blink_thread.is_alive():
            self.blink_thread.join(timeout=1.0)

    def clear_screen(self):
        """화면 전환 시 화면 초기화"""
        self.recent_canvas.itemconfig(self.origin_image_place, state="hidden")
        self.recent_canvas.itemconfig(self.ok_image_place, state="hidden")
        self.recent_canvas.itemconfig(self.ng_image_place, state="hidden")
        self.blink_off()
        self.clickable_areas = []

    def make_show_origin_image(self, image, inspection_coords, detection_coords):
        """원본 이미지 표시 : /3 크기로 축소 (한글 라벨 표시, 좌표 표시, 랜덤색상)"""
        try:
            font = ImageFont.truetype("C:/Windows/Fonts/malgunbd.ttf", 48)
        except:
            font = ImageFont.load_default()

        # OpenCV 이미지를 PIL로 변환
        pil_img = Image.fromarray(cv2.cvtColor(image, cv2.COLOR_BGR2RGB))
        draw = ImageDraw.Draw(pil_img)

        # 클릭 가능한 영역 정보 저장 (1/3 크기로 리사이즈된 좌표)
        self.clickable_areas = []

        # 분류 검사 영역 표시
        if inspection_coords:
            for idx, (key, value) in enumerate(inspection_coords.items()):
                x, y, w, h = int(value[1]), int(value[2]), int(value[3]), int(value[4])
                x0, y0 = x, y
                x1, y1 = x + w, y + h
                color = self.color_palette[idx % len(self.color_palette)]
                draw.rectangle([x0, y0, x1, y1], outline=color, width=7)
                text_bbox = draw.textbbox((x0, y0), str(key), font=font)
                text_height = text_bbox[3] - text_bbox[1] + 15
                draw.text((x0, y0 - text_height - 5), str(key), fill=color, font=font)
                
                # 1/3 크기로 리사이즈된 좌표 저장
                resized_x0, resized_y0 = x0 // 3, y0 // 3
                resized_x1, resized_y1 = x1 // 3, y1 // 3
                self.clickable_areas.append({
                    'key': key,
                    'coords': [resized_x0, resized_y0, resized_x1, resized_y1]
                })

        # 각인 검사 영역 표시
        if detection_coords:
            x, y, w, h = int(detection_coords[0]), int(detection_coords[1]), int(detection_coords[2]), int(detection_coords[3])
            x0, y0 = x, y
            x1, y1 = x + w, y + h
            color = self.color_palette[-1]
            draw.rectangle([x0, y0, x1, y1], outline=color, width=7)
            text_bbox = draw.textbbox((x0, y0), "각인 검사", font=font)
            text_height = text_bbox[3] - text_bbox[1] + 15
            draw.text((x0, y0 - text_height - 5), "각인 검사", fill=color, font=font)
            
            # 1/3 크기로 리사이즈된 좌표 저장
            resized_x0, resized_y0 = x0 // 3, y0 // 3
            resized_x1, resized_y1 = x1 // 3, y1 // 3
            self.clickable_areas.append({
                'key': 'engrave',
                'coords': [resized_x0, resized_y0, resized_x1, resized_y1]
            })

        # PIL 이미지를 1/3로 리사이즈
        width, height = pil_img.size
        new_width = width // 3
        new_height = height // 3
        resized_image = pil_img.resize((new_width, new_height), Image.LANCZOS)
        resized_image = ImageTk.PhotoImage(resized_image)
        return resized_image

    def select_part(self):
        """검사 영역 선택"""
        self.state = 'second'
        self.recent_canvas.itemconfig(self.BG, image=self.second_bg)
        origin_image_path = f'recent_images/{MB.model_name}/{self.selected_client_id}/origin/origin.jpg'
        origin_image = cv2.imread(origin_image_path)
        if origin_image is None:
            messagebox.showerror("오류", f"{self.selected_client_id}의 원본 이미지가 없습니다.\n검사를 시작하면 자동으로 원본 이미지가 저장됩니다.")
            return

        inspection_coords = model_info['models'][MB.model_name][self.selected_client_id]['inspection_coords']
        detection_coords = model_info['models'][MB.model_name][self.selected_client_id]['detection_coords']
        self.show_origin_image = self.make_show_origin_image(origin_image, inspection_coords, detection_coords)
        self.recent_canvas.itemconfig(self.origin_image_place, image=self.show_origin_image, state="normal")
    
    def select_area(self):
        """검사 영역 선택"""
        self.state = 'third'
        self.clear_screen()
        self.recent_canvas.itemconfig(self.BG, image=self.third_bg)

        ok_folder = f'recent_images/{MB.model_name}/{self.selected_client_id}/{self.selected_area_name}/ok'
        ng_folder = f'recent_images/{MB.model_name}/{self.selected_client_id}/{self.selected_area_name}/ng'

        self.ok_images = self.get_sorted_image_list(ok_folder)
        self.ng_images = self.get_sorted_image_list(ng_folder)

        self.ok_index = 0
        self.ng_index = 0

        self.show_ok_image()
        self.show_ng_image()

    def get_sorted_image_list(self, folder_path):
        """이미지 파일 목록 조회"""
        image_files = []
        for ext in ('*.jpg', '*.png'):
            image_files.extend(glob.glob(os.path.join(folder_path, ext)))
        # 파일 수정시간 기준 내림차순 정렬 (최신이 앞)
        image_files.sort(key=os.path.getmtime, reverse=True)
        return image_files

    def show_ok_image(self):
        if self.ok_images:
            img = Image.open(self.ok_images[self.ok_index])
            img = img.resize((597, 597), Image.LANCZOS)
            self.ok_photo = ImageTk.PhotoImage(img)
            self.recent_canvas.itemconfig(self.ok_image_place, image=self.ok_photo, state="normal")
        else:
            self.recent_canvas.itemconfig(self.ok_image_place, image="", state="hidden")

    def show_ng_image(self):
        if self.ng_images:
            img = Image.open(self.ng_images[self.ng_index])
            img = img.resize((597, 597), Image.LANCZOS)
            self.ng_photo = ImageTk.PhotoImage(img)
            self.recent_canvas.itemconfig(self.ng_image_place, image=self.ng_photo, state="normal")
        else:
            self.recent_canvas.itemconfig(self.ng_image_place, image="", state="hidden")


if __name__ == "__main__":
    base_path = os.path.dirname(os.path.abspath(__file__))
    folder_name = os.path.basename(base_path)
    line_type = folder_name.split("_")[0].lower()  # cone, cup
    line_name = folder_name.split("_")[1]  # SS9
    client_num = 6 if line_type == 'cone' else 5
    line_config = get_line_config(line_type)
    print(f"Hello, I am {line_type} from {line_name}. Did you call me?")
    print(f"Now, I shall open my {client_num} eyes")
    
    # 모델 정보 로드
    with open('config/info.json', 'r', encoding='utf-8') as f:
        model_info = json.load(f)

    root = tk.Tk()
    LM = LogManager()
    SS = SocketServer('192.168.50.9', 9999)
    MB = Modbus()
    DB = MySql(LM, line_config)
    MF = MainFrame(master=root)
    HW = HardWork()
    HF = HistoryFrame(master=root)
    AF = AdminFrame(master=root)
    RN = RecentNgCheckFrame(master=root)
    ER = ExcelReportGenerator(LM, DB, line_type, line_name)

    threading.Thread(target=MB.read_signal_thread, daemon=True).start()
    threading.Thread(target=MB.send_signal_thread, daemon=True).start()
    threading.Thread(target=SS.connect_thread, daemon=True).start()
    threading.Thread(target=SS.message_sender, daemon=True).start()
    threading.Thread(target=HW.check_mail_send_time, daemon=True).start()


    root.protocol("WM_DELETE_WINDOW", MF.on_closing)
    MF.tkraise()
    root.mainloop()





