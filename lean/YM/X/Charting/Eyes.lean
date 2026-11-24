import YM.X.Charting.Pink
/-!
Geometry away estimates for one insertion relative to all eyes. Inverse-square and tail. Unified mask mode.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Hinge
open Function Filter Set Metric MeasureTheory Lattice Wilson PertExtension PertExtension.Series PertExtension.Series.Radial
open Source ProjectorNext.Calibration Gauss Next.Rank Normal MvPolynomial Finsupp
open Feyn Gauge LatticePT PertExtension.Orb Chart Stems PertExtension.Series.Tested Finset Interval Size Asymptotics
open Pert.Orb (positiveLinks wilson Potential)
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {n:Side} {q:ℕ+}(hq:1<q.val)
local notation "X'"=> MvPolynomial.X
variable {α β V:Type*}
local notation "K"=> (atTop:Filter ℕ)

def border (q:ℕ+)(d i:ℕ):ℕ:= q.val^(i*d)
lemma cost_border (q:ℕ+)(d i:ℕ): (↑(border q d i):ℝ)=magnify q i^d:= by unfold border magnify;rw [← pow_mul];push_cast;rfl
lemma at_border (q:ℕ+) (d i:ℕ): ticket q (d:ℤ) i=(border q d i:ℝ):= (ticket_nat q d i).trans (cost_border q d i).symm
@[simp] lemma border_pos (q:ℕ+)(d i:ℕ): 0<border q d i:=pow_pos q.pos _
include hq
lemma at_border_high {d:ℕ}(h:0<d): Tendsto (border q d) atTop atTop:= by
   apply (tendsto_natCast_atTop_iff (R:=ℝ)).mp; simp_rw [cost_border]; exact (tendsto_pow_atTop h.ne').comp (giant hq) -- name

lemma risen {f:ℕ→ℝ}(h:Charged q f): ∀ᶠ d:ℕ in atTop, ∀ᶠ k in K,‖f k‖* 8 ≤ border q d k:= by
   obtain ⟨j,h⟩:=h; let b:= j.natAbs; obtain ⟨c,hc,hc'⟩:= (Ripe.enlarge h (show j≤(b:ℤ) by omega)).exists_pos
   filter_upwards [eventually_gt_atTop b] with d hd; filter_upwards [hc'.bound,(giant hq).eventually (eventually_ge_atTop (8*c))] with k hF h'
   rw [ticket_nat,Real.norm_of_nonneg (show 0≤ magnify q k ^ b from pow_nonneg (amp_pos .. |>.le) _)] at hF; change ‖f k‖*8 ≤ _; rw [cost_border]; let v:=magnify q k; change 8*c≤v at h'; calc
      _ ≤ c*v^b*8:= by gcongr
      _ ≤ v^(b+1):= by rw [pow_succ]; nlinarith [pow_nonneg (amp_pos q k).le b] -- loosen
      _ ≤ _ := pow_le_pow_right₀ (cane q k) hd

def Capt (d:ℕ)(x y:Beam q) := ∀ᶠ k in K, separation (x k) (y k)*8 ≤ border q d k
lemma near_capt {x y:Beam q}(h:Near x y): ∀ᶠ d:ℕ in atTop,Capt d x y:= (risen hq (show Charged _ (raysD x y) from h)).mono (fun d hd=>hd.mono (fun k hk=> by unfold raysD at hk; rw [Real.norm_of_nonneg (by positivity)] at hk; exact_mod_cast hk))

omit hq
def second (p:PlaqAxes)(x:Site n): Site n:= -x-step p.val.1-step p.val.2
lemma second₂ (p:PlaqAxes)(x:Site n): second p (second p x)=x:= by unfold second; abel
def minmass (o z:Site n) (p:PlaqAxes)(a:Bool) := if a then min (ticketN o z) (ticketN o (second p z)) else ticketN o z
def moon (d:ℕ)(p:PlaqAxes)(a:Bool)(v:Beam q)(i:ℕ)(z:Site (side q i)):ℝ := if border q d i < minmass (v i) z p a then (minmass (v i) z p a:ℕ) else 1
lemma moon_nat (p:PlaqAxes)(v:Beam q)(a:Bool)(i d:ℕ)(z): if border q d i< minmass (v i) z p a then moon d p a v i z≥ (minmass (v i) z p a:ℕ) else moon d p a v i z=1:= by unfold moon;split_ifs<;>simp
lemma moon_le (p:PlaqAxes)(v:Beam q)(a:Bool)(i d:ℕ)(z): moon d p a v i z ≤ (minmass (v i) z p a:ℝ):= by unfold moon;split_ifs; exact le_rfl; rw [Nat.one_le_cast]; cases a <;> simp [minmass,ticketN]
lemma moon_pos (p:PlaqAxes)(v:Beam q)(a:Bool)(i d:ℕ)(z): 1≤moon d p a v i z:= by unfold moon; split_ifs with h; exact Nat.one_le_cast.mpr ((border_pos q d i).trans h); exact le_rfl -- casts natPos trans h :0<
lemma minmass₀ (p:PlaqAxes)(a:Bool)(x y:Site n):minmass x y p a≤ticketN x y:= by cases a<;> simp [minmass]

lemma closer (x y u v:Site n) {d d₁ d₂:ℕ}(h:separation u x*2≤d)(hv:separation y v≤d₁)(h':d+d₂≤ticketN u y)(g:d₁*4≤ticketN u y): ticketN u y ≤ 4* ticketN x v:= by
   have ht:= separation_triangle u x y; have he:= separation_triangle x v y; rw [separation_comm v] at he; unfold ticketN at *; omega
lemma place_near (x:Site n)(i : Hair G): separation x (place x i).1.1 ≤ rounds i.1.1:= by change separation x (wrap _ _ +x) ≤ _; rw [separation_comm,separation,add_sub_cancel_right]; apply round_fee
lemma reversePlace (p:PlaqAxes)(x:Site n)(j: Hair G): (reverseK (place x j)).1.1 = wrap n (step p.val.1+step p.val.2- j.1.1-step j.1.2) + second p x:= by change -(wrap n j.1.1+x)- step j.1.2=_; unfold second; rw [map_sub, map_sub, map_add, wrap_step,wrap_step, wrap_step]; abel

include hq
-- v taken ANY offset whose separation bounded by fixed r
lemma near_eye_bound (p : PlaqAxes)(a:Bool)(o z x : Beam q)(i:Hair G)(Z Y: Beam q)(j:ℕ) (t:∀ k,separation (Z k) (Y k)≤ j)(v:∀ k,minmass (o k) (z k) p a≤ticketN (o k) (Z k)) (d:ℕ)(hd:0<d)(h:Capt d o x): ∀ᶠ k:ℕ in K, moon d p a o k (z k) ≤ 4*mass (Y k) (place (x k) i).1.1:= by
   let w k := (place (x k) i).1.1; let l:=rounds i.1.1; filter_upwards [h,(at_border_high hq hd).eventually (eventually_ge_atTop (4*l+4*j))] with k hk he
   unfold moon;split; next hy=>
     change ↑(minmass (o k) (z k) p a)≤ (4:ℝ)*(ticketN (Y k) (w k))
     have h1 : separation (o k) (w k)*2 ≤ border q d k:= by have hp:=place_near (x k) i; have ht:= separation_triangle (o k) (x k) (w k); unfold l at he; unfold w at *; omega
     have h2 : border q d k+0≤ticketN (o k) (Z k) := Nat.add_zero _ ▸ hy.le.trans (v k)
     have h3: j*4≤ticketN (o k) (Z k):= by omega
     have ht:= (v k).trans (closer (w k) (Z k) _ (Y k) h1 (t k) h2 h3); change _≤4*(separation (w k) (Y k)+1) at ht; rw [separation_comm (w k)] at ht; exact_mod_cast ht
   exact one_le_mul_of_one_le_of_one_le (by norm_num) (mass_pos ..)
end YM.PositionX.Hinge
