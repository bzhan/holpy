"""Setup flask app."""

from flask import Flask
from flask_cors import CORS
from flask.json import JSONEncoder as _JSONEncoder
from flask import Flask as _Flask

class JSONEncoder(_JSONEncoder):
    def default(self, o):
        if hasattr(o, 'keys') and hasattr(o, '__getitem__'):
            return dict(o)
        else:
            return super().default(o)

class Flask(_Flask):
    json_encoder = JSONEncoder

app = Flask(__name__, static_url_path='/static')
CORS(app)
app.secret_key = b'_5#y2L"F4Q8z\n\xec]/'