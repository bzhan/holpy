import io,sys
import json


file_path = 'library/logic_base.json'
def save_file(data):
    with open(file_path, 'r+', encoding='utf-8') as f:
        file_data = json.load(f)
        if file_data !=data:
            data = file_data + data
            j = open(file_path, 'w+', encoding='utf-8')
            json.dump(data, j)
            j.close()
        f.close()





