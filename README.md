# An Implementation of Coron's Reformulation of Coppersmith's Algorithm for Bivariate Polynomials

## Example

You need to provide an irreducible bivariate polynomial

```python
R.<x,y> = ZZ[]
f1 = 127*x*y - 1207*x - 1461*y + 21
```

as well as bounds for the solutions and a parameter k

```python
X, Y = 30, 20
k = 2
```

Then we can call the solver

```python
bivariate_solver(f1, X, Y, k)
```

which returns the solutions

```python
[(21, 21), (23, 19)]
```


## License

This project is licensed under the MIT license.
