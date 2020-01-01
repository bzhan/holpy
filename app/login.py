# Author: Wenfan Zhou, Bohua Zhan

"""API for register and login."""

import json, os, sqlite3, shutil
from flask import request
from flask.json import jsonify

from logic import basic
from app.app import app


@app.route('/api/login', methods=['POST'])
def login():
    """Login for an user.

    Input:
    * username: username
    * password: password

    Returns:
    * result: success - login is successful.
    * result: failed - login failed (username / password do not match).

    """
    data = json.loads(request.get_data().decode('utf-8'))
    username = data['username']
    password = data['password']
    for k in get_users():
        if username == k[1] and password == str(k[2]):
            user_list = os.listdir('./users')
            if username != 'master' and username not in user_list:
                shutil.copytree('./library', basic.user_dir(username))

            return jsonify({'result': 'success'})

    return jsonify({'result': 'failed'})


@app.route('/api/register', methods=['POST'])
def register():
    """Register a new user.

    Input:
    * username: username
    * password: password

    Returns:
    * result: success - registration is successful.
    * result: failed - registration failed (user already exists).

    """
    data = json.loads(request.get_data().decode('utf-8'))
    username = data['username']
    password = data['password']
    for k in get_users():
        if username == k[1]:
            return jsonify({'result': 'failed'})

    if username and password:
        add_user(username, password)

    return jsonify({'result': 'success'})


DATABASE = os.getcwd() + '/users/user.db'

def add_user(username, password):
    """Add new user to the database."""
    with sqlite3.connect(DATABASE) as conn:
        cursor = conn.cursor()
        cursor.execute('insert into users(name, password) values("'+ username +'","'+ password +'");')
        cursor.close()
        conn.commit()

def init_user():
    """Create users table."""
    with sqlite3.connect(DATABASE) as conn:
        cursor = conn.cursor()
        cursor.execute('create table users(id auto_increment,name CHAR(50) not null,password CHAR(50) not null);')
        cursor.close()
        conn.commit()

def get_users():
    """Get list of username-password from the database."""
    with sqlite3.connect(DATABASE) as conn:
        cursor = conn.cursor()
        cursor.execute('select * from users;')
        results = cursor.fetchall()
        cursor.close()
        conn.commit()
    return results

@app.route('/api/refresh-files', methods=['POST'])
def refresh_files():
    """Replace user data with library data.

    Input:
    * username: username.

    """
    data = json.loads(request.get_data().decode("utf-8"))
    username = data['username']
    if username != 'master':
        shutil.rmtree(basic.user_dir(username))
        shutil.copytree('./library', basic.user_dir(username))

    return jsonify({})
