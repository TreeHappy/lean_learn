# Math behind the browser sandbox

`web/index.html` is a self-contained Three.js page. It uses the same surface
and geodesic rule as the Lean code, then adds two extra layers:

* **pinball mode** — shoot a geodesic and watch the marble roll along it;
* **walk mode** — push the marble around with gravity, friction and keyboard
  forces, while keeping the rolling constraint exact.

This note derives every formula the page uses. It is written to match the
variable names in the script, so you can read it side by side with the source.
For the proof that the geodesic rule really is the geodesic equation, see
[`shooting-method.md`](./shooting-method.md); the Lean definitions live in
`lean/Brane/Shooting.lean` and `lean/Brane/DifferentialGeometry.lean`.

## Notation

| Symbol | Meaning | Code |
|---|---|---|
| $(x,y)$ | coordinates on the parameter plane | `player.x`, `player.y` |
| $h(x,y)$ | height of the surface | `heightAt` |
| $h_x,h_y$ | first derivatives | `derivativesAt` |
| $H$ | Hessian $\begin{pmatrix}h_{xx}&h_{xy}\\h_{xy}&h_{yy}\end{pmatrix}$ | `derivativesAt` |
| $\mathbf v=(\dot x,\dot y)$ | velocity in parameter coordinates | `walk.s[2]`, `walk.s[3]` |
| $g_{ij}$ | first fundamental form (metric) | implicit in `ginvTimes` |
| $g^{ij}$ | inverse metric | `ginvTimes` |
| $\mathbf n$ | unit surface normal | `surfaceFrame` |
| $\mathbf c$ | centre of the marble in 3D | `marble.position` |
| $r$ | marble radius, `0.16` | `MARBLE_R` |
| $\boldsymbol\omega$ | angular velocity of the marble | `rollBy` |
| $Q$ | orientation quaternion | `player.q` |

The world is z-up: the parameter plane is the $xy$-plane and height is $z$.

---

## 1. The surface

The terrain is a sum of nine anisotropic Gaussians. Each bump $b$ has height
$a_b$, centre $(c_{bx},c_{by})$ and width parameter $\sigma_b^2$:

$$
h(x,y)=\sum_b a_b\exp\!\left(-\frac{(x-c_{bx})^2+(y-c_{by})^2}{\sigma_b^2}\right).
$$

`a: (i % 3 === 0 ? -1 : 1) * (0.5 + Math.random() * 1.1)` makes every third
bump a crater, so the player gets hills and bowls.

Writing $d_x=x-c_{bx}$, $d_y=y-c_{by}$, $E_b=a_b e^{-(d_x^2+d_y^2)/\sigma_b^2}$,
one Gaussian contributes

$$
\begin{aligned}
h_x &= E_b\left(-\frac{2d_x}{\sigma_b^2}\right), &
h_y &= E_b\left(-\frac{2d_y}{\sigma_b^2}\right),\\
h_{xx} &= E_b\left(\frac{4d_x^2}{\sigma_b^4}-\frac{2}{\sigma_b^2}\right),\\
h_{xy} &= E_b\left(\frac{4d_xd_y}{\sigma_b^4}\right),\\
h_{yy} &= E_b\left(\frac{4d_y^2}{\sigma_b^4}-\frac{2}{\sigma_b^2}\right).
\end{aligned}
$$

Summing over bumps gives `derivativesAt`. Computing the value and all five
derivatives from the same exponential is both cheaper and more consistent
than finite differences.

---

## 2. Geometry of a graph

The surface is parametrized by

$$
\mathbf X(x,y)=(x,\;y,\;h(x,y)),\qquad
\mathbf X_x=(1,0,h_x),\quad \mathbf X_y=(0,1,h_y).
$$

The induced metric (first fundamental form) is

$$
g_{ij}=\mathbf X_i\cdot\mathbf X_j=\delta_{ij}+h_i h_j,
\qquad
G=\begin{pmatrix}1+h_x^2 & h_xh_y\\ h_xh_y & 1+h_y^2\end{pmatrix},
$$

with determinant $\det G=1+h_x^2+h_y^2\ge 1$ and inverse

$$
G^{-1}=\frac{1}{1+h_x^2+h_y^2}
\begin{pmatrix}1+h_y^2 & -h_xh_y\\ -h_xh_y & 1+h_x^2\end{pmatrix}.
$$

That inverse is exactly `ginvTimes(hx, hy, gx, gy)`.

The unit normal is

$$
\mathbf n=\frac{(-h_x,-h_y,1)}{\sqrt{1+h_x^2+h_y^2}}.
$$

### Christoffel symbols

For a graph, $\partial_i\partial_j\mathbf X=(0,0,h_{ij})$ and
$\mathbf X_k\cdot\partial_i\partial_j\mathbf X=h_k h_{ij}$. Hence

$$
\Gamma^k_{ij}=g^{kl}h_l h_{ij}
            =\bigl(G^{-1}\nabla h\bigr)^k h_{ij}.
$$

Contracting with $v^iv^j$ gives

$$
\Gamma^k_{ij}v^iv^j
=\bigl(G^{-1}\nabla h\bigr)^k
 \underbrace{(v^iv^j h_{ij})}_{=\mathbf v^{\mathsf T}H\mathbf v}.
$$

So the geodesic equation $\ddot q^k+\Gamma^k_{ij}\dot q^i\dot q^j=0$ becomes

$$
\boxed{\;\ddot{\mathbf q}=-G^{-1}\bigl((\mathbf v^{\mathsf T}H\mathbf v)\,\nabla h\bigr)\;}
$$

which is `geoAccel`. The quantity $\mathbf v^{\mathsf T}H\mathbf v$ is the
normal curvature of the surface in the direction of travel; the factor
$G^{-1}\nabla h$ converts the resulting normal acceleration back into
parameter coordinates.

---

## 3. Pinball mode: shooting and RK4

A shot is the initial value problem

$$
\mathbf s=(\dot x,\dot y,\ddot x,\ddot y)
         =(x,y,v_x,v_y),\qquad
\dot{\mathbf s}=(v_x,v_y,\texttt{geoAccel}_x,\texttt{geoAccel}_y).
$$

The launch velocity is $s(d_x,d_y)$ where $s\in[0.3,4.2]$ comes from the drag
length (capped at $2.4$) and $\mathbf d$ is the normalized drag direction.
The integrator is classical Runge–Kutta 4:

$$
\begin{aligned}
\mathbf k_1 &= \mathbf f(\mathbf s),&
\mathbf k_2 &= \mathbf f(\mathbf s+\tfrac{\Delta t}{2}\mathbf k_1),\\
\mathbf k_3 &= \mathbf f(\mathbf s+\tfrac{\Delta t}{2}\mathbf k_2),&
\mathbf k_4 &= \mathbf f(\mathbf s+\Delta t\,\mathbf k_3),\\
\mathbf s_{n+1} &= \mathbf s_n+\frac{\Delta t}{6}
  (\mathbf k_1+2\mathbf k_2+2\mathbf k_3+\mathbf k_4).
\end{aligned}
$$

The step is $\Delta t=0.02$ (`SHOOT_DT`) and integration stops when
$|x|$ or $|y|$ exceeds `EXT + 0.5 = 3.7`. The precomputed UV samples are the
geodesic; the marble is drawn at the sample reached at time $t$, using linear
interpolation between samples. Its velocity for the rolling step is estimated
from neighbouring samples as $\mathbf v\approx
(\mathbf p_{i+1}-\mathbf p_i)/\Delta t$.

### Dot spacing

The trail is resampled by **arc length**, not by sample index. With chord
lengths $d_i=\sum_{k\le i}\|\mathbf p_k-\mathbf p_{k-1}\|$ in 3D, dot $k$ is
placed at arclength $kL/(n-1)$ and linearly interpolated. This keeps dots
evenly spaced even where the integrator takes unevenly sized steps. Dot size
and alpha taper with the trail parameter $t=k/(n-1)$:
`size = base·(0.28 + 0.72t)` and
`alpha = a·(0.35 + 0.65·smoothstep(t, 0, 0.18))`.

---

## 4. Walk mode: adding forces

The kinetic and potential energies are

$$
T=\tfrac12 m\,\mathbf v^{\mathsf T}G\mathbf v,
\qquad U=mg\,h(x,y).
$$

Lagrange's equations give

$$
\frac{d}{dt}\frac{\partial T}{\partial \dot q^i}
-\frac{\partial T}{\partial q^i}=-\frac{\partial U}{\partial q^i}+Q_i,
$$

which expands to

$$
G_{ij}\ddot q^j+\Gamma_{ijk}\dot q^j\dot q^k
=-mg\,h_i+Q_i.
$$

Raising the index with $G^{-1}$ and dividing by $m$:

$$
\ddot{\mathbf q}
=-G^{-1}\bigl((\mathbf v^{\mathsf T}H\mathbf v+g)\nabla h\bigr)
+G^{-1}\mathbf f,
\qquad \mathbf f=Q/m.
$$

This is `walkAccel`: the first term is the old geodesic curvature plus gravity,
the second term is the applied force raised to an acceleration.

### Keyboard force

A key press defines a desired horizontal direction $\mathbf d$ from the
camera's forward/right vectors projected onto the $xy$-plane. To make it a
force that acts *on the surface*, project it onto the tangent plane:

$$
\mathbf F = P\,\bigl(\mathbf d-(\mathbf d\cdot\mathbf n)\mathbf n\bigr),
$$

with $P=$ `PUSH` (multiplied by $1.8$ when Shift is held). A 3D force becomes a
generalized force through the Jacobian of $\mathbf X$:

$$
f_x=\mathbf F\cdot\mathbf X_x=F_x+F_z h_x,\qquad
f_y=\mathbf F\cdot\mathbf X_y=F_y+F_z h_y.
$$

### Friction and braking

Rolling friction is modelled as a tangential force proportional to the
surface velocity, $\mathbf F_{\text{fric}}=-c\,\dot q^i\mathbf X_i$. Its
generalized force is $-cG_{ij}\dot q^j$, so after raising indices the
acceleration is simply $-k\mathbf v$ with $k=c/m$ (`FRICTION = 0.9`).
Holding Space adds `BRAKE = 5.0` to $k$.

The complete ODE integrated at a fixed $\Delta t=1/120$ with the same RK4
scheme is therefore

$$
\ddot{\mathbf q}
=G^{-1}\!\begin{pmatrix}
f_x-(\mathbf v^{\mathsf T}H\mathbf v+g)h_x\\
f_y-(\mathbf v^{\mathsf T}H\mathbf v+g)h_y
\end{pmatrix}
-k\mathbf v .
$$

### Boundary

When $|x|$ or $|y|$ exceeds `EXT - 0.12`, the coordinate is clamped and the
normal velocity is reflected with restitution $e=$ `RESTITUTION`:

$$
x\mapsto \operatorname{clamp}(x),\qquad
\dot x\mapsto -e\,\dot x .
$$

---

## 5. The rolling marble

Let the contact point on the surface be $\mathbf p=(x,y,h)$ and the sphere
centre be

$$
\mathbf c=\mathbf p+r\mathbf n .
$$

For a sphere rolling without slipping, the material point at the contact has
zero velocity. That point is at $\mathbf c-r\mathbf n$, so

$$
\mathbf v_c+\boldsymbol\omega\times(-r\mathbf n)=0
\quad\Longrightarrow\quad
\mathbf v_c=r\,\boldsymbol\omega\times\mathbf n .
$$

Crossing with $\mathbf n$ and choosing zero spin about $\mathbf n$ gives

$$
\boxed{\;\boldsymbol\omega=\frac{\mathbf n\times\mathbf v_c}{r}\;}
$$

This is the constraint used in `rollBy`. It is physically consistent with
torque integration: for a solid sphere $I=\tfrac25mr^2$ and a tangential
contact force $\mathbf F_t$,

$$
\boldsymbol\tau=(-r\mathbf n)\times\mathbf F_t,\qquad I\dot{\boldsymbol\omega}=\boldsymbol\tau,
$$

and the friction needed to enforce $\mathbf v_c=r\boldsymbol\omega\times\mathbf n$
is exactly the contact force in section 4. Enforcing the constraint directly
avoids numerical slip.

### Centre velocity on a graph

Differentiating $\mathbf c=\mathbf p+r\mathbf n$ needs $\dot{\mathbf n}$. Let

$$
a=h_{xx}\dot x+h_{xy}\dot y,\qquad
b=h_{xy}\dot x+h_{yy}\dot y,\qquad
q=\sqrt{1+h_x^2+h_y^2}.
$$

Since $\mathbf n=(-h_x,-h_y,1)/q$ and $\dot q=(h_xa+h_yb)/q$,

$$
\dot{\mathbf n}
=\frac{(-a,-b,0)}{q}-\mathbf n\,\frac{h_xa+h_yb}{q^2}.
$$

The surface point moves with $\dot{\mathbf p}=(\dot x,\dot y,h_x\dot x+h_y\dot y)$,
so

$$
\mathbf v_c=\dot{\mathbf p}+r\dot{\mathbf n}.
$$

`rollBy` computes this $\mathbf v_c$, then $\boldsymbol\omega$, from the
current position, velocity and Hessian.

### Orientation update

The orientation $Q$ maps marble-body coordinates to world coordinates. For a
world-frame angular velocity $\boldsymbol\omega$,

$$
\dot Q=\tfrac12(0,\boldsymbol\omega)\,Q .
$$

For constant $\boldsymbol\omega$ over a step $\Delta t$, with
$\theta=\lVert\boldsymbol\omega\rVert\Delta t$ and
$\hat{\boldsymbol\omega}=\boldsymbol\omega/\lVert\boldsymbol\omega\rVert$,
the exact update is

$$
\Delta Q=\left(\cos\frac\theta2,\;
 \hat{\boldsymbol\omega}\sin\frac\theta2\right),\qquad
Q_{n+1}=\operatorname{normalize}(\Delta Q\,Q_n).
$$

`Quaternion.premultiply` implements the left multiplication because the
angular velocity is expressed in **world** coordinates. The sphere texture
has wedges, rings and a pole dot, so this rotation is visible: a marble
travelling downhill spins about an axis perpendicular to its direction of
travel, and the spin axis tilts with the surface normal.

---

## 6. Rendering math

* **Colour ramp.** Heights are normalized with
  $t=(h-h_{\min})/(h_{\max}-h_{\min})$ and mapped by piecewise linear
  interpolation through nine Catppuccin Latte colours
  `blue → sky → teal → green → yellow → peach → pink → mauve → lavender`.
  The ramp is stored per vertex in a `color` attribute and multiplied by the
  material's lighting in the shader.

* **Contour bands.** Let $d=\bigl|14t-\operatorname{round}(14t)\bigr|$ be the
  distance to the nearest contour level in normalized height. The vertex
  colour is scaled by
  $0.82+0.18\,\operatorname{smoothstep}(d,0.02,0.12)$, giving fourteen subtle
  darker bands across the height range. Grid lines use $0.55\times$ the ramp
  colour so they read as ink on the bright surface.

* **Lighting.** Normals come from `computeVertexNormals()` on the triangulated
  graph. The diffuse part of `MeshStandardMaterial` is proportional to
  $\max(0,\mathbf n\cdot\mathbf l)$ for the directional light, with ambient and
  hemisphere contributions filling in the shadows. Fog interpolates linearly
  towards the background between distances 14 and 32.

* **Contact ring and shadow.** The ring and shadow are flat meshes whose
  quaternion is `setFromUnitVectors((0,0,1), n)`, so they lie in the surface's
  tangent plane at the marble's contact point.

* **Glow and alpha.** Sprites use radial gradients sampled as textures; the
  point shader discards fragments outside a disc and multiplies the trail
  alpha by `uOpacity`. Ghost trails decay by setting that uniform to
  $0.16+0.1i$ for older trails.

---

## 7. Constants at a glance

| Constant | Value | Role |
|---|---:|---|
| `EXT` | 3.2 | half-size of the terrain domain |
| `SHOOT_DT` | 0.02 | RK4 step for geodesics |
| `GRAVITY` | 2.2 | downhill acceleration $g$ |
| `PUSH` | 4.5 | keyboard force magnitude |
| `FRICTION` | 0.9 | rolling friction rate $k$ |
| `BRAKE` | 5.0 | extra damping while Space is held |
| `RESTITUTION` | 0.55 | energy kept at a boundary bounce |
| `MARBLE_R` | 0.16 | sphere radius |
| `FIXED_DT` | 1/120 | fixed timestep for walk mode |
| `MAX_DOTS` | 160 | maximum dots in one trail |

All units are scene units; the equations are scale-invariant except for the
explicit constants above.

## Further reading

* [`shooting-method.md`](./shooting-method.md) — derives the geodesic rule,
  compares Euler and RK4, and explains the shooting interpretation.
* `lean/Brane/DifferentialGeometry.lean` — the Lean definition of the metric,
  Christoffel symbols and normal for a graph.
* `lean/Brane/Shooting.lean` — the polymorphic `geoAccel`, `rk4Step` and
  `shoot` pipeline that the browser page mirrors.
