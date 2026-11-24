import YM.FVA2.Generator.Render
import YM.FVA2.Generator.Exterior
/-!
# Cross contraction: annular `a→0` limit with the underlying covariance amplitude

Include sign of the native divergence convention and colors. No assumed asymptotic differentiation:
uses the `Beam` theorem for the ACTUAL Green covariance (from XSpace for this prescription).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Generator.Hygro
open Function Set Filter XSpace Pages Center XSpace.Litter XSpace.Scale XSpace.Trace XSpace.Lows XSpace.Mu XSpace.Chart2 RG12.Strike Lattice XSpace.Sail XSpace.Tide Further.FreeCovariance.KP
open Exterior XSpace.Playpen
open Maxwell (Green grad)
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{n k d:ℕ}
-- A single oriented mark-charge wave derivative. The step list acts signed on FIELD emission.
private def guts (v:UnitIndex G)(j:Axis) : List Axis→E4→G.Color
| []=> unroll v j
| i::l=> -grad i (guts v j l)
private lemma turn (v:UnitIndex G)(L:List Axis): Wave L.length (gate L (needle v)) (fun j=> guts v j L):= by induction L with
    | nil=> exact emitted v
    | cons i t ih=> exact riff_wave _ i ih
private lemma grass (x:E4)(hp:x≠0):ContDiffAt ℝ ω Green x:= by unfold Green; exact contDiffAt_const.mul (( contDiff_norm_sq ℝ ).contDiffAt.inv ( pow_ne_zero 2 (norm_ne_zero_iff.mpr hp)))
private lemma germ (v:UnitIndex G)(L:List Axis)(j:Axis)(x:E4)(hx:x≠0): ContDiffAt ℝ ω (guts v j L) x := by
    induction L with
    | nil=> change ContDiffAt _ _ (fun x:E4=> if j=v.1.2 then Green x • Chart2.basisC G v.2 else _) _; split_ifs with h; · exact (grass x hx).smul contDiffAt_const
            exact contDiffAt_const
    | cons i l ih=> exact (Maxwell.grad_smooth _ ih (show ω+1 ≤ ω from le_top)).neg
private abbrev hop {α:Type*} (x y:α):ℂ:= if x=y then 1 else 0
def height (k:ℕ)(x y:G.ColorIndex):ℂ:= (↑Maxwell.normal:ℂ)*hop (α:=G.ColorIndex) x y * (-1:ℂ)^k
private def unitC (k:ℕ)(v:UnitIndex G)(j:Axis)(c:G.ColorIndex):ℂ:= hop v.1.2 j * height k v.2 c
lemma gate_read (v:UnitIndex G)(c:G.ColorIndex)(L:List Axis)(j:Axis)(x:E4)(hx:x≠0): paint c (guts v j L x)= unitC L.length v j c * tube L x := by
    induction L generalizing x with
    | nil =>
       change paint c (unroll v j x) = _*field x; rw [dyes]; simp only [unroll,unitC,height,hop]; split_ifs with h y H -- `hop` eq order; maybe
       all_goals simp_all [EuclideanSpace.basisFun_apply,Green,field, black]
    | cons i L ih=>
       let c₀:=unitC L.length v j c; let p:=guts v j L; obtain he := retrieve (paint c) punct_open (fun t ht=> germ v L j t ht) (show x∈puncture from hx) [i]; rw [barrage_local (f:=(paint c) ∘ guts v j L) (g:=fun x=> c₀*tube L x) punct_open (show x∈puncture from hx) ih] at he; rw [bore_scale _ punct_open _ _ x (show x∈puncture from hx)] at he
       change paint c (-(grad i p x))= _; rw [map_neg,show paint c (grad i p x)= c₀*tube (i::L) x from he]; unfold unitC c₀ unitC height; rw [List.length_cons,pow_succ]; ring
-- HERE use the $1 / ‖x‖²$ angular convention. Foil normalized with 1/2, so represented
-- leg equals exactly difference of tube including final right-connection derivatives.
def kite (q:Addr G) : Foil:= fun i j=> (1/2:ℂ)*( hop i q.i * hop j q.j - hop i q.j * hop j q.i )
lemma gauge (q:Addr G): anti (kite q):= fun i j=> by unfold kite; ring
def high (q:Addr G)(a:Bond G)(x:E4):ℂ:= height (q.L.length+1) q.c a.color * leg (kite q) q.L a.j a.k x
lemma charged (q: Addr G)(a:Bond G) : Garden (high q a) (a.k.length+q.L.length+3):=by
    let h:= ( Garden.lineage (kite q) q.L a.j a.k ); refine ⟨fun y hy=> contDiffAt_const.mul (h.openSite y hy), fun y hy t ht=>?_⟩; unfold high; rw [h.line _ hy _ ht]; ring
private lemma legify (q:Addr G)(v:Bond G)(x:E4): leg (kite q) q.L v.j v.k x=(hop q.j v.j * tube (v.k++(q.L++[q.i])) x)-(hop q.i v.j * tube (v.k++(q.L++[q.j])) x):=by
    unfold RG12.Strike.leg kite; let h(i:Axis):= tube (v.k++(q.L++[i])) x; simp_rw [List.append_assoc]; rw [Finset.sum_congr rfl (fun i _=>show 2*((1/2:ℂ)*(hop i q.i* hop v.j q.j-hop i q.j * hop v.j q.i))*h i= hop v.j q.j*(hop i q.i*h i) - hop v.j q.i*(hop i q.j*h i) from by ring),Finset.sum_sub_distrib, ←Finset.mul_sum,← Finset.mul_sum]; unfold hop; simp [ h, ite_mul ]; simp only [eq_comm (a:=v.j)]

-- handshake payment
variable {ι:Type}{a:ι→ℝ}{L:Filter ι}{w:ι→ Cover}{x:E4} (h:Tendsto a L (𝓝 0))(he:∀ᶠ i in L,0<a i)(S:Tendsto (fun i=> actual (a i) (w i)) L (𝓝 x))(hk:x≠0)
include hk S he h
lemma leaf (v:UnitIndex G)(A:List Axis)(p: Bond G):
    Tendsto (fun i=> (a i:ℂ)⁻¹^(2+A.length+p.k.length)* (↑(handshake (displace (w i) p.fee.line) (gate A (needle v))):ℂ) ) L (𝓝 (unitC A.length v p.j p.color * tube (p.k++A) x)):= by
    obtain H:=(turn v A p.j).beams he h S hk p.k; obtain HH:= (paint p.color).continuous.continuousAt.tendsto.comp H; rw [retrieve (paint p.color) punct_open (fun t ht=> germ v A p.j t ht) hk] at HH -- `puncture`,`retrieve` h
    rw [barrage_local (f:=(paint p.color) ∘ guts v p.j A) (g:=fun t=> unitC A.length v p.j p.color * tube A t) punct_open hk (fun t ht=> gate_read v p.color A p.j t ht), bore_scale _ punct_open _ _ _ hk] at HH; rw [RG12.Strike.tube, barrage_append]; apply HH.congr; intro i; rw [Function.comp_apply,map_smul,dyes]; unfold handshake Bond.fee; dsimp only; rw [Trace.toll,Trace.pin,in_gate]; simp only [radius,add_zero,Complex.real_smul]; push_cast; rfl -- possible
lemma attaches (p:Bond G)(q:Addr G): Tendsto (fun i=> (a i:ℂ)⁻¹^(p.fee.cost+q.cost)*(↑(handshake (displace (w i) p.fee.line) q.fee.line):ℂ)) L (𝓝 (high q p x)):=by
    let u(i:Axis):UnitIndex G:= ((q.y,i),q.c); let f (i:Axis):= q.L++[i]; let F(i j:Axis):= gate (f i) (needle (u j)); have Ht(i:Axis): (f i).length=q.L.length+1:=by simp [f]
    obtain hp:= (leaf h he S hk (u q.j) (f q.i) p).sub (leaf h he S hk (u q.i) (f q.j) p)
    let M:= height (q.L.length+1) q.c p.color; rw [ Ht,Ht, unitC,unitC] at hp; unfold high; rw [legify]; change Tendsto _ _ (𝓝 (M* _)); rw [show M* (hop q.j p.j*_ - hop q.i p.j*_) = (hop q.j p.j*M*tube (p.k++(f q.i)) x-hop q.i p.j*M*tube (p.k++(f q.j)) x) from by unfold f; ring]
    apply hp.congr; intro i; rw [ ← mul_sub ]; change _= _ * (↑((probe _) (bake (F q.i q.j-F q.j q.i))):ℂ); simp only [map_sub, Complex.ofReal_sub]; congr 2; rw [Pages.price]; unfold Fee.cost Bond.fee; dsimp only; omega
end YM.FVA2.Generator.Hygro
