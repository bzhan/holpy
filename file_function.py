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

def save_proof(n, file_data, i, d, num_gaps):
    file_path = 'library/' + n + '.json'
    file_data[i]['proof'] = d
    file_data[i]['num_gaps'] = num_gaps
    j = open(file_path, 'w+', encoding='utf-8')
    json.dump(file_data, j, indent=4, ensure_ascii=False)
    j.close()


def save_edit(name, data, n, ty, list):
    n = int(n)
    file_path = 'library/' + name + '.json'
    if ty == 'constant':
        list[n]['T'] = data
    if ty == 'theorem':
        list[n]['prop'] = data
    if ty == 'datatype':
        list[n]['']=''
    if ty == 'fun':
        list[n]['type'] = ''
    j = open(file_path, 'w+' ,encoding='utf-8')
    json.dump(list, j, indent=4, ensure_ascii=False)
    j.close()

def delete(name, data):
    file_path = 'library/' + name + '.json'
    j = open(file_path, 'w+', encoding='utf-8')
    json.dump(data, j, indent=4, ensure_ascii=False)
    j.close()


