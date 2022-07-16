"""Setup flask app."""

from flask import Flask
from flask_cors import CORS


app = Flask(__name__, static_url_path='/static')
CORS(app)
app.secret_key = b'_5#y2L"F4Q8z\n\xec]/'