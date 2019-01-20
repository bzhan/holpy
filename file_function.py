import io,sys
import json


global file_data_temp
file_data_temp = {}
def fun_open(name):
    file_path = 'library/' + name + '.json'
    with open(file_path, 'r+', encoding='utf-8') as f:
        file_data = json.load(f)
        for i in range(len(file_data)):
            file_data_temp[i] = file_data[i]
        f.close()

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

def save_proof(n, i, d, num_gaps):
    file_path = 'library/' + n + '.json'
    with open(file_path, 'r+', encoding='utf-8') as f:
        file_data = json.load(f)
        file_data[i]['proof'] = d
        file_data[i]['num_gaps'] = num_gaps
        j = open(file_path, 'w+', encoding='utf-8')
        json.dump(file_data, j, indent=4, ensure_ascii=False)
        j.close()
        f.close()

def save_edit(name, data, n, ty):
    list = []
    n = int(n)
    file_path = 'library/' + name + '.json'
    if ty == 'constant':
        file_data_temp[n]['T']=data
    if ty == 'theorem':
        file_data_temp[n]['prop'] = data
    if ty == 'datatype':
        file_data_temp[n]['']=''
    if ty == 'fun':
        file_data_temp[n]['type'] = ''
    for i in file_data_temp.values():
        list.append(i)
    j = open(file_path, 'w+' ,encoding='utf-8')
    json.dump(file_data_temp, j, indent=4, ensure_ascii=False)
    j.close()

def delete(name, n):
    file_path = 'library/' + name + '.json'
    with open(file_path, 'r+', encoding='utf-8') as f:
        file_data = json.load(f)
        del file_data[n]
        j = open(file_path, 'w+', encoding='utf-8')
        json.dump(file_data, j, indent=4, ensure_ascii=False)
        j.close()
        f.close()

