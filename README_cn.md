## holpy

用Python实现高阶逻辑。

这个项目使用Python 3。

需要的包：

Lark解析器：https://github.com/lark-parser/lark

文件夹结构：

* [`kernel`](kernel/)：高阶逻辑内核。
  * [`type`](kernel/type.py)：代表HOL类型的数据类型。
  * [`term`](kernel/term.py)：代表HOL项的数据类型。
  * [`thm`](kernel/thm.py)：代表HOL定理的数据类型，包括基本的推理规则。
  * [`proof`](kernel/proof.py)：证明的线形表达，由一个序列的给内核的指令组成。
  * [`macro`](kernel/macro.py)：宏，用户定义的证明方法。
  * [`theory`](kernel/theory.py)：理论状态，包括类型和常数的签名，和公理和定理的列表。
  * [`extension`](kernel/extension.py): 理论的扩展。
  * [`report`](kernel/report.py)：检验理论扩展时产生的调试信息和统计。

* [`logic`](logic/)：基础逻辑和基本的自动化。
  * [`basic`](logic/basic.py)：基础逻辑的定义和基本证明方法。
  * [`matcher`](logic/matcher.py)：项的匹配。
  * [`proofterm`](logic/proofterm.py)：证明的树状表达。用于方便地产生证明，并且可以转换成线形表达。
  * [`conv`](logic/conv.py)：变换的定义。

* [`syntax`](syntax/)：语法解析和打印。
  * [`printer`](syntax/printer.py)：打印功能。
  * [`parser`](syntax/parser.py)：词法解析功能，使用Lark解析器。

* [`server`](server/)：最高层功能。
  * [`server`](server/server.py)：最高层证明检验。
