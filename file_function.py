import io,sys
import json


def save_file(name, d):
    file_path = 'library/' + name + '.json'
    with open(file_path, 'r+', encoding='utf-8') as f:
        file_data = json.load(f)
        if file_data !=d:
            d = file_data + d
            j = open(file_path, 'w+', encoding='utf-8')
            json.dump(d, j, indent=4, ensure_ascii=False)
            j.close()
        f.close()

def save_proof(n, i, d):
    file_path = 'library/' + n + '.json'
    with open(file_path, 'r+', encoding='utf-8') as f:
        file_data = json.load(f)
        file_data[i]['save-proof'] = d
        j = open(file_path, 'w+', encoding='utf-8')
        json.dump(file_data, j, indent=4, ensure_ascii=False)
        j.close()
        f.close()








