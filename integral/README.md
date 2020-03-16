## Verification of symbolic computation of definite integrals.

Use

```python -m integral.run_integral```

to run all tests.

The user interface is a part of the combined user interface for holpy. To start,
change to /app folder. Then run ```npm install``` followed by ```npm run serve```,
then start the server (in the root directory) using ```python app.py```,
and go to page ```localhost:8080```.

There is also a tutorial for the user interface in /integral/tutorial.

We primarily used three references:

* Exam preparation in higher mathematics, Tongji University, 7th edition
* MIT integration bee: http://www.mit.edu/~pax/integrationbee.html
* UCDAVIS calculus page problems list: https://www.math.ucdavis.edu/~kouba/ProblemsList.html

All indefinite integrals in the references above are converted to
definite integrals with appropriately chosen limits of integration.

Examples covered so far (more to be added in the future):

* Tongji: 36/36
* MIT Integration bee:
  * 2013: 20/25
* UCDAVIS problems list:
  * U-substitution: 17/18
  * Exponentials: 8/12
  * Trigonometric: 27/27
  * Integration by parts: 22/23
  * Logarithms and Arctangent: 20/22
  * Partial fraction: 16/20

Total: 166/183 (90.7%)
