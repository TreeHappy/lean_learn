# ODEs for the game, without the fear factor

This note is about the **numerical** side of the physics in
`web/index.html`. If "ODE" sounds intimidating, read it as:

> An ODE is a rule that says: *given where you are now, which way are you
> moving, and how fast are you changing?*

That is all. The game has a computer repeatedly asking that question and
taking a small step. This note explains the asking and the stepping.

The full geometry is in [`game-math.md`](./game-math.md); the geodesic proof is
in [`shooting-method.md`](./shooting-method.md). Here we stay close to the code.
The Lean twin of the numerical code is
[`lean/Brane/GamePhysics.lean`](../lean/Brane/GamePhysics.lean).

---

## 1. A second-order law becomes a four-number state

Newton's laws are usually written with acceleration:

$$
\ddot q = A(q, \dot q).
$$

Here $q=(x,y)$ is the marble's position on the parameter plane, $\dot q=(v_x,v_y)$
its velocity, and $A$ the acceleration the surface and forces produce.
A computer does not know what "acceleration" *is*; it only knows how to update
numbers. So we bundle position and velocity into one state:

$$
s = (x, y, v_x, v_y).
$$

Now the second-order equation becomes a first-order equation:

$$
\dot s = \big(v_x,\; v_y,\; A_x(s),\; A_y(s)\big).
$$

This is the trick behind almost all game physics. In the browser code this is
the little function inside `rk4Step`:

```js
const f = (st) => {
  const [ax, ay] = accel(st[0], st[1], st[2], st[3]);
  return [st[2], st[3], ax, ay];
};
```

The first two entries just copy velocity into position change; the last two
are the force law. The Lean version is `GamePhysics.field`:

```lean
def field (accel : State → Float × Float) (s : State) : State :=
  ⟨s.vx, s.vy, (accel s).1, (accel s).2⟩
```

### Where the game's states live

| Game quantity | JavaScript | Lean |
|---|---|---|
| state | `s = [x, y, vx, vy]` | `State` structure |
| pinball acceleration | `geoAccel` | `geoAccel` |
| walk acceleration | `walkAccel` | `walkAccelWith` |
| state derivative | `f` inside `rk4Step` | `field` |
| one RK4 step | `rk4Step` | `rk4Step` |
| trajectory | array of UV samples | `samples` |

---

## 2. Taking steps: Euler and RK4

Let $f(s)=\dot s$ and let $\Delta t$ be a small time step.

**Explicit Euler** uses one slope measurement:

$$
s_{n+1}=s_n+\Delta t\, f(s_n).
$$

It is easy, but it assumes the slope stays constant for the whole step. On a
curved hill that assumption is visibly wrong.

**Classical RK4** takes four measurements and averages them with weights
$1:2:2:1$:

$$
\begin{aligned}
k_1 &= f(s_n),\\
k_2 &= f(s_n+\tfrac{\Delta t}{2}k_1),\\
k_3 &= f(s_n+\tfrac{\Delta t}{2}k_2),\\
k_4 &= f(s_n+\Delta t\,k_3),\\
s_{n+1} &= s_n+\frac{\Delta t}{6}(k_1+2k_2+2k_3+k_4).
\end{aligned}
$$

Think of it as: look at the slope at the start, twice near the middle, and once
at the end, then take a weighted average. That is why RK4 hugs curved paths
much better than Euler.

### A tiny numeric experiment

Take the decay law $\dot v=-v$, $v(0)=1$. The exact answer after one second is
$e^{-1}\approx0.3679$.

| Method | Step | Result after 1 s |
|---|---:|---:|
| Euler | $\Delta t=0.1$ | 0.3487 |
| Euler | $\Delta t=0.5$ | 0.2500 |
| RK4 | $\Delta t=0.5$ | 0.3682 |
| exact | — | 0.3679 |

Two lessons:

* smaller steps help;
* a good method (RK4) helps even more than a small step.

The game uses RK4 with $\Delta t=0.02$ for shots and a fixed $\Delta t=1/120$
for walking.

### Local and global error

* **Local error** is the mistake in one step.
* **Global error** is the accumulated mistake after many steps.

RK4 has local error $O(\Delta t^5)$ and global error $O(\Delta t^4)$. In plain
words: halving the step divides the global error by about $16$. Euler has
global error $O(\Delta t)$: halving the step only halves the error.

There is a stability limit too. For the decay test above, Euler with
$\Delta t>2$ overshoots and oscillates. In the game, friction is $k=0.9$, so
$\Delta t=1/120$ gives $k\Delta t\approx0.0075$ — comfortably safe.

---

## 3. The game's acceleration laws

### Pinball: no forces, just curved coordinates

The pinball field is

$$
\ddot{\mathbf q}=-G^{-1}\bigl((\mathbf v^{\mathsf T}H\mathbf v)\,\nabla h\bigr).
$$

Read it like this:

1. $\mathbf v^{\mathsf T}H\mathbf v$ measures how much the surface bends in
   the direction of travel.
2. $\nabla h$ points uphill.
3. Multiplying them gives the acceleration needed to keep the marble on the
   surface instead of flying off its tangent plane.
4. $G^{-1}$ converts that surface acceleration back into $(x,y)$ coordinates.

If the surface were flat, $H=0$ and the acceleration would be zero: a straight
line at constant speed. On the bumpy terrain, "straightest possible" looks
curved when drawn in the $(x,y)$ parameter plane.

### Walk: gravity, push and friction

Walk mode adds ordinary forces:

$$
\ddot{\mathbf q}
=G^{-1}\!\begin{pmatrix}
f_x-(\mathbf v^{\mathsf T}H\mathbf v+g)h_x\\
f_y-(\mathbf v^{\mathsf T}H\mathbf v+g)h_y
\end{pmatrix}
-k\mathbf v .
$$

The three new pieces:

| Term | What it does |
|---|---|
| $-gG^{-1}\nabla h$ | gravity: rolls downhill |
| $G^{-1}f$ | your WASD push, projected onto the surface |
| $-k\mathbf v$ | rolling friction: you coast to a stop |

The JS `walkAccel` and Lean `walkAccelWith` are the same formula. The Lean
version takes `g` and `k` as arguments so we can state the "no forces"
sanity check:

```lean
theorem walkAccelWith_zero (bumps : Array Bump) (s : State) :
    walkAccelWith 0 0 bumps (0, 0) s = geoAccel bumps s := by
  sorry
```

The `sorry` means: *we know this should be true, but we are not proving it
yet*.

---

## 4. Why the game uses a fixed step

Browsers call animation frames at irregular times. Feeding the raw frame time
into RK4 would make the physics depend on your monitor refresh rate. Instead,
the game accumulates time and consumes it in equal chunks:

```js
walk.acc += dt;
while (walk.acc >= FIXED_DT && steps < 8) {
  stepWalk(FIXED_DT);
  walk.acc -= FIXED_DT;
  steps++;
}
```

This gives reproducible physics. The cap of 8 steps stops a lagging tab from
freezing the page trying to catch up.

For pinball shots the step is already baked into the precomputed path
(`SHOOT_DT = 0.02`); the animation just walks along that array. This is a
common trick: **simulate once, render many times**.

### Turning states into a visible trail

A trajectory is an array of states. The renderer lifts each $(x,y)$ to
$(x,y,h(x,y))$ and resamples by arc length so dots stay evenly spaced. The
marble follows the same array with linear interpolation between samples.

### Edge behaviour

Walk mode uses a square domain $|x|,|y|\le 3.08$. When a step leaves it, the
coordinate is clamped and the normal velocity is reflected with restitution
$0.55$. In Lean this is `bounce`; in the page it is the loop inside
`stepWalk`.

---

## 5. Rolling is another ODE

The marble's rotation is not cosmetic. It is governed by its own first-order
equation on orientations.

For a sphere of radius $r$ with centre velocity $\mathbf v_c$ and surface
normal $\mathbf n$, no-slip rolling gives

$$
\boldsymbol\omega = \frac{\mathbf n\times\mathbf v_c}{r}.
$$

On a graph the centre is $\mathbf p+r\mathbf n$, so

$$
\mathbf v_c=(\dot x,\dot y,h_x\dot x+h_y\dot y)+r\dot{\mathbf n},
$$

and $\dot{\mathbf n}$ comes from the Hessian. The Lean code spells this out
as `normalDot`, `centerVelocity` and `angularVelocity`.

The orientation quaternion $Q$ then satisfies

$$
\dot Q=\tfrac12(0,\boldsymbol\omega)Q.
$$

This is just another ODE. For constant $\boldsymbol\omega$ over a step, the
exact update is

$$
Q_{n+1}=\mathrm{normalize}(\Delta Q\,Q_n),\qquad
\Delta Q=\left(\cos\frac\theta2,\;\hat{\boldsymbol\omega}\sin\frac\theta2\right),
$$

with $\theta=\|\boldsymbol\omega\|\Delta t$. The JavaScript calls this
`premultiply` because $\boldsymbol\omega$ is expressed in world coordinates.
The wedges on the texture exist so you can actually see $Q$ changing.

---

## 6. Running the Lean version

From the repository root:

```console
cd lean
lake env lean Brane/GamePhysics.lean
```

To see a concrete trajectory, put this in any Lean file that imports the
module:

```lean
import Brane.GamePhysics
open Brane.GamePhysics

#eval demoShot
```

which prints the first six states of a pinball shot:

```text
#[{ x := -1.600000, y := -1.600000, vx := 0.500000, vy := 0.200000 },
  { x := -1.590012, y := -1.596008, vx := 0.498806, vy := 0.199148 },
  { x := -1.580048, y := -1.592034, vx := 0.497598, vy := 0.198284 },
  { x := -1.570108, y := -1.588077, vx := 0.496376, vy := 0.197408 },
  { x := -1.560193, y := -1.584138, vx := 0.495142, vy := 0.196522 },
  { x := -1.550302, y := -1.580216, vx := 0.493897, vy := 0.195624 }]
```

Notice how `vx` and `vy` change slowly even though no force was added: the
curved coordinates themselves produce an acceleration.

### Things worth trying

1. Change `dt` from `0.02` to `0.2` and watch RK4 start to struggle.
2. Replace `rk4Step` with `eulerStep` in `demoShot` and compare.
3. Set `push` to a constant like `(1, 0)` and watch gravity fight it.
4. Turn friction off by calling `walkAccelWith gravity 0 ...`.

---

## 7. Mental checklist when something looks wrong

* Did I put **velocity** in the state, not just position?
* Is my step size small compared with how fast the field changes?
* Am I using a fixed step, independent of frame rate?
* Did I convert a physical force into generalized coordinates with $G^{-1}$?
* For rolling, did I use the **centre** velocity $\mathbf v_c$ rather than the
  parameter velocity $(v_x,v_y)$?
* Did I normalize the quaternion after each update?

## Further reading

* [`game-math.md`](./game-math.md) — derivations of every formula used here.
* [`shooting-method.md`](./shooting-method.md) — why the geodesic rule is a
  geodesic, and why RK4 beats Euler.
* `lean/Brane/GamePhysics.lean` — executable numerical core with `sorry` lemmas.
