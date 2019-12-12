## holpy

高阶逻辑的Python实现。

### 安装与使用

本项目需要Python 3.5。安装项目依赖的包裹，使用：

```python -m pip install -r requirements.txt```

所有后端的单元测试在```*/tests/*_test.py```文件里.

项目的前端使用Vue实现。启动前端的步骤是：首先切换到./app文件夹，
然后使用```npm install```和```npm run serve```。然后在根文件夹
使用```python app.py```启动服务。最后打开页面```localhost:8080```。

### 文件夹结构：

* [`kernel`](kernel/)：高阶逻辑内核。
  * [`type`](kernel/type.py)：HOL类型的数据类型。
  * [`term`](kernel/term.py)：HOL项的数据类型。
  * [`thm`](kernel/thm.py)：HOL定理的数据类型，包括基本推理规则。
  * [`proof`](kernel/proof.py)：证明的线形表达，由一个序列的给内核的指令组成。
  * [`macro`](kernel/macro.py)：宏，用户定义的证明方法。
  * [`theory`](kernel/theory.py)：理论状态，包括类型和常数的签名，和公理和定理的列表。
  * [`extension`](kernel/extension.py): 理论的扩展。
  * [`report`](kernel/report.py)：检验理论扩展时产生的调试信息和统计。

* [`logic`](logic/)：基础逻辑和基本的自动化。
  * [`matcher`](logic/matcher.py)：项的匹配。
  * [`proofterm`](logic/proofterm.py)：证明的树状表达。用于方便地产生证明，并且可以转换成线形表达。
  * [`conv`](logic/conv.py)：变换的定义。
  * [`logic`](logic/logic.py)：关于逻辑的基本工具和宏。
  * [`basic`](logic/basic.py)：导入理论的工具。

* [`data`](data/)：常用数据类型。
  * [`nat`](data/nat.py)：自然数。
  * [`function`](data/function.py)：函数。
  * [`list`](data/list.py)：列表。
  * [`set`](data/set.py)：集合。
  * [`real`](data/real.py)：实数。

* [`syntax`](syntax/)：语法解析和打印。
  * [`operator`](syntax/operator.py)：一元和二元运算符的数据。
  * [`infertype`](syntax/infertype.py)：类型推导。
  * [`printer`](syntax/printer.py)：打印功能。
  * [`parser`](syntax/parser.py)：词法解析功能，使用Lark解析器。

* [`server`](server/)：最高层功能
  * [`server`](server/server.py)：证明状态上的基本操作。
  * [`tactic`](server/tactic.py)：策略的定义。
  * [`method`](server/method.py)：方法的定义。

* [`app`](app/)：网页前端。
  * [`__init__.py`](app/__init__.py)：服务程序。

* [`library`](library/)：理论库
