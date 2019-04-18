
:math:`\newcommand{\To}{\Rightarrow}`

.. code:: ipython3

    import os, sys
    sys.path.append(os.path.split(os.getcwd())[0])

.. code:: ipython3

    from kernel.type import HOLType, TVar, Type, TFun, boolT
    from logic.nat import natT

Types
-----

In higher-order logic, every term has a type. Common types include
booleans, natural numbers, functions, lists, and so on. We also need the
concept of *type variables*. Types are implemented in
``kernel/type.py``.

Booleans and natural numbers are type constants that do not take any
parameters. They can be constructed as follows:

.. code:: ipython3

    print(Type("bool"))


.. parsed-literal::

    bool


.. code:: ipython3

    print(Type("nat"))


.. parsed-literal::

    nat


We use ``boolT`` as a shortcut for ``Type("bool")``, and ``natT`` as a
shortcut for ``Type("nat")``.

.. code:: ipython3

    print(boolT)
    print(natT)


.. parsed-literal::

    bool
    nat


Functions is a very important class of types. Given any two types
:math:`A` and :math:`B`, the type :math:`A \To B` represents functions
from :math:`A` to :math:`B`. For example, the type :math:`nat \To bool`
represents functions from natural numbers to booleans, or in other
words, properties of natural numbers. This type is constructed as
follows:

.. code:: ipython3

    print(Type("fun", natT, boolT))


.. parsed-literal::

    nat => bool


A shortcut to construct function types is to use ``TFun``:

.. code:: ipython3

    print(TFun(natT, boolT))


.. parsed-literal::

    nat => bool


A key concept for dealing with function types is *currying*. It allows
us to represent functions of multiple arguments. For example, the type
of functions taking two natural numbers as arguments, and output one
natural number, is given by :math:`nat \To (nat \To nat)`. Note this is
very different from :math:`(nat \To nat) \To nat`. Since the former is
used more frequently, we have the convention that the operator
:math:`\To` associates to the right, so the former type is simply
written as :math:`nat \To nat \To nat`. In general, the type
:math:`A_1 \To \cdots \To A_n \To C` can be read as: functions taking
arguments of type :math:`A_1,\dots A_n` as input, and output a value of
type :math:`C`.

.. code:: ipython3

    print(TFun(natT, TFun(natT, natT)))


.. parsed-literal::

    nat => nat => nat


``TFun`` can actually take any number of arguments:

.. code:: ipython3

    print(TFun(natT, natT, natT))


.. parsed-literal::

    nat => nat => nat


Functions are not the only types with arguments. Given any type
:math:`A`, we can form the type of (finite) lists with entries in
:math:`A`:

.. code:: ipython3

    print(Type("list", natT))


.. parsed-literal::

    nat list


All these can be combined in arbitrary ways. For example, the following
is a type representing lists of functions that take a list of natural
numbers as input, and returns a natural number:

.. code:: ipython3

    print(Type("list", TFun(Type("list", natT), natT)))


.. parsed-literal::

    (nat list => nat) list


A few methods are defined for working with function types: -
``is_fun()`` returns whether the type is a function type. - Given a type
:math:`A \To B`, ``domain_type()`` returns :math:`A` and
``range_type()`` returns :math:`B`. - Given a type
:math:`A_1 \To\cdots\To A_n\To B`, ``strip_type()`` returns the pair
:math:`[A_1,\dots,A_n], B`.

.. code:: ipython3

    a = TFun(natT, boolT)
    print(a.is_fun())
    print(boolT.is_fun())
    print(a.domain_type())
    print(a.range_type())
    print(a.strip_type())
    
    b = TFun(natT, natT, boolT)
    print(b.strip_type())


.. parsed-literal::

    True
    False
    nat
    bool
    ([Type(nat, [])], Type(bool, []))
    ([Type(nat, []), Type(nat, [])], Type(bool, []))


Type variables
--------------

A *type variable* is a variable that can stand in for any type. We
follow the convention of writing a type variable with name :math:`a` as
``'a``. Type variables are constructed as follows:

.. code:: ipython3

    print(TVar("a"))


.. parsed-literal::

    'a


Type variables can be used as arguments to type constructors. For
example, the following type represents all functions from type :math:`a`
to type :math:`b`:

.. code:: ipython3

    print(TFun(TVar("a"), TVar("b")))


.. parsed-literal::

    'a => 'b


Next, we introduce the important concepts of *substitution* and
*matching*. A type with type variables can be considered as a *pattern*
for producing types. If each type variable in the pattern is assigned a
concrete value, the pattern can be *instantiated* to a concrete type
(without type variables). We illustrate this with some examples.

.. code:: ipython3

    p = TFun(TVar("a"), TVar("b"))
    print(p)
    print(p.subst({"a": natT, "b": boolT}))
    print(p.subst({"a": TFun(natT, natT), "b": boolT}))
    print(p.subst({"a": natT, "b": TFun(natT, boolT)}))


.. parsed-literal::

    'a => 'b
    nat => bool
    (nat => nat) => bool
    nat => nat => bool


In fact, we can assign a type variable to another type containing type
variables. Note in this case, substitution of all variables is performed
at the same time.

.. code:: ipython3

    print(p.subst({"a": TVar("b"), "b": TVar("a")}))


.. parsed-literal::

    'b => 'a


Matching can be considered as the dual of substitution. Given a pattern
:math:`p` (a type containing type variables) and a type :math:`t` (with
or without type variables), it determines whether :math:`p` can be
instantiated to :math:`t`, and returns the assignment of type variables
in :math:`p` if it is possible.

.. code:: ipython3

    print(p.match(TFun(natT, boolT)))


.. parsed-literal::

    {'a': Type(nat, []), 'b': Type(bool, [])}


If it is impossible to instantiate :math:`p` to :math:`t`, the match
function throws a ``TypeMatchException``:

.. code:: ipython3

    p.match(natT)  # throws TypeMatchException


::


    ---------------------------------------------------------------------------

    TypeMatchException                        Traceback (most recent call last)

    <ipython-input-22-abed19d645ef> in <module>()
    ----> 1 p.match(natT)  # throws TypeMatchException
    

    ~/Private/holpy/kernel/type.py in match(self, T)
        172         """
        173         tyinst = dict()
    --> 174         self.match_incr(T, tyinst)
        175         return tyinst
        176 


    ~/Private/holpy/kernel/type.py in match_incr(self, T, tyinst)
        159         elif self.ty == HOLType.TYPE:
        160             if T.ty != HOLType.TYPE or T.name != self.name:
    --> 161                 raise TypeMatchException()
        162             else:
        163                 for arg, argT in zip(self.args, T.args):


    TypeMatchException: 


Note the same type variable can appear multiple times in a pattern.
During matching, each occurrence of the type variable must be assigned
to the same type.

.. code:: ipython3

    q = TFun(Type("list", TVar("a")), TVar("a"))
    print(q)
    print(q.subst({"a": natT}))
    print(q.match(TFun(Type("list", natT), natT)))


.. parsed-literal::

    'a list => 'a
    nat list => nat
    {'a': Type(nat, [])}


Here is an example of a matching that failed because the two occurrences
of ``'a`` correspond to different types (:math:`nat` and :math:`bool`).

.. code:: ipython3

    q.match(TFun(Type("list", natT), boolT))


::


    ---------------------------------------------------------------------------

    TypeMatchException                        Traceback (most recent call last)

    <ipython-input-23-df35534a7d76> in <module>()
    ----> 1 q.match(TFun(Type("list", natT), boolT))
    

    ~/Private/holpy/kernel/type.py in match(self, T)
        172         """
        173         tyinst = dict()
    --> 174         self.match_incr(T, tyinst)
        175         return tyinst
        176 


    ~/Private/holpy/kernel/type.py in match_incr(self, T, tyinst)
        162             else:
        163                 for arg, argT in zip(self.args, T.args):
    --> 164                     arg.match_incr(argT, tyinst)
        165         else:
        166             raise TypeError()


    ~/Private/holpy/kernel/type.py in match_incr(self, T, tyinst)
        154             if self.name in tyinst:
        155                 if T != tyinst[self.name]:
    --> 156                     raise TypeMatchException()
        157             else:
        158                 tyinst[self.name] = T


    TypeMatchException: 


Miscellaneous functions
-----------------------

``name`` can be used to access the name of a type variable or
constructor. ``args`` can be used to access the list of arguments
(returned as a tuple):

.. code:: ipython3

    a = TVar("a")
    print(a.name)
    
    b = Type("list", natT)
    print(b.name)
    print(b.args)


.. parsed-literal::

    a
    list
    (Type(nat, []),)


``get_tvars()`` returns the list of type variables in a type.
``get_tsubs()`` returns the list of all types appearing in a type.

.. code:: ipython3

    a = TFun(TVar("a"), TVar("b"), natT)
    print(", ".join(str(t) for t in a.get_tvars()))
    print(", ".join(str(t) for t in a.get_tsubs()))


.. parsed-literal::

    'a, 'b
    'a => 'b => nat, 'a, 'b => nat, 'b, nat

