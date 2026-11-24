import YM.XSpace.Suburbs

/-!
# Bare amplitudes through first order, after unconditioning from `Removal`

X-space Taylor operator section, giving the precise polynomials. Nobody has altered `W`
on these original positions; compensations (elsewhere) prove *existence* of convergence
in one position scheme via change-of-frame before changing perturbative parameter.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Foundation
open Filter Set Function Lattice Chart2 Mu Trace Furlough Comets Comets.Input JetGauge PowerSeries Next.Rank.Normal Contraction Stall Outline Shade
open scoped Topology BigOperators
variable {I:Type}[DecidableEq I]{G:Gauge}
variable {n:ℕ}
abbrev Form (G:Gauge)(d:I→ℕ):= ∀ i,On.Grade G (d i)
variable (W:Initialize G){d:I→ℕ}(s:Finset I)(p:Form G d) (a:ℝ) (x:I→Cover)
def base (a:ℝ):ℂ:= (a:ℂ)⁻¹
def slack (x:Cover)(p:On.Grade G n):= Trace.volume x (Prelude.enter0 (W.surveys n) p)
def snaps (v:On.Grade G n)(x:Cover)(a:ℝ):= base a^n • slack W x v
def stars (x: Cover)(p:On.Grade G n):=Trace.volume x (Prelude.mark1 (W.surveys n) p)
def sess := ∏ i∈s, freeze (snaps W (p i) (x i) a)
abbrev initial (i:I):= W.surveys (d i)
abbrev road (i:I):=Prelude.startField (initial W (d:=d) i) (p i)
def baseZero := E (Mu.root G) (sess W s p a x)
def LText (y:Cover): Module.Dual ℂ (Stamp G):= (E (Mu.root G)) ∘ₗ LinearMap.mulRight ℂ (sess W s p a x) ∘ₗ freeze ∘ₗ (Trace.volume y).toLinearMap
lemma cold (x:Cover)(u:On.Grade G n): constantCoeff (toy (W.surveys n) x (Prelude.startField (W.surveys n) u).val)=freeze (slack W x u):= by rw [slack,← move_reel (W.surveys n) (Price.preparedL u).val x]; exact Encore.opens ..
lemma hot (x:Cover)(u:On.Grade G n): coeff 1 (toy (W.surveys n) x (Prelude.startField (W.surveys n) u).val)=freeze (stars W x u):=by
  let S:=W.surveys n; let v:=(Prelude.startField S u).val; change p1 S x v=_; unfold stars Prelude.mark1; rw [← show flicker (Trace.volume x (p1 S 0 v))= Trace.volume x (flicker _) from meant ..,came,Trace.stained,Chart.pull1];simp [Chart.lug]
lemma pill : constantCoeff (crop s (initial W (d:=d)) (fun i=>(road W p i).val) x)= ∏ i∈s,freeze (slack W (x i) (p i)):=by unfold crop; rw [map_prod]; exact Finset.prod_congr rfl fun i _=> cold ..
lemma stage0 : sess W s p a x= base a ^ (∑ i∈s,d i) • constantCoeff (crop s (initial W (d:=d)) (fun i=>(road W p i).val) x) :=by rw [pill]; induction s using Finset.induction_on with | empty=> simp [sess] | insert i s hi ih=> unfold sess at *; rw [Finset.sum_insert hi, Finset.prod_insert hi, Finset.prod_insert hi,snaps,map_smul,ih,pow_add,smul_mul_smul]
lemma stage_book : baseZero W s p a x=base a^(∑ i∈s,d i) * Encore.zeroReading (initial W (d:=d)) (fun i=>(road W p i).val) s x:=by rw [baseZero, stage0,map_smul];rfl
private lemma fps (U:I→PowerSeries (Stamp G)) : coeff 1 (∏ i∈s,U i)=∑ i∈s,(coeff 1 (U i))*constantCoeff (∏ j∈s.erase i,U j):=by
  induction s using Finset.induction_on with
  | empty=> simp
  | insert i s hi ih=>
      rw [Finset.prod_insert hi,coeff_one_mul,ih,Finset.sum_insert hi,Finset.erase_insert hi]; congr 1; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j hj=>?_ ; have hn:i≠j:=by rintro rfl; contradiction
      rw [Finset.erase_insert_of_ne hn,Finset.prod_insert (by simp [hi]), map_mul]; ring
lemma stage1 : base a^(∑ i∈s,d i) • coeff 1 (crop s (initial W (d:=d)) (fun i=>(road W p i).val) x)=
    ∑ i∈s, freeze (base a^(d i) • stars W (x i) (p i))*sess W (s.erase i) p a x:= by
  unfold crop; rw [fps,Finset.smul_sum]; apply Finset.sum_congr rfl; intro i hi; rw [stage0,map_smul,smul_mul_smul, ← Finset.add_sum_erase _ _ hi, pow_add]; rw [show coeff 1 (toy (initial W i (d:=d)) (x i) (road W p i).val)= _ from hot W (x i) (p i)];rfl

def sends (f:Face ℤ)(P:Stamp G):= E (Mu.root G) (V3 G f*P)
lemma matching (q:PlaqAxes)(u:Cover): sends (u,q) (sess W s p a x)=base a^(∑ i∈s,d i)*Comets.witness (u,q) (Outline.dusk G) x (Comets.Input.work s (initial W (d:=d)) (fun i=>(road W p i).val)):=by rw [sends,stage0,election s (initial W (d:=d)) (fun i=>(road W p i).val) (Outline.dusk G), mul_smul_comm,map_smul];rfl
lemma sweeping (q:PlaqAxes): Summable fun u:Cover=> sends (u,q) (sess W s p a x):=by simp_rw [matching]; exact (full_cover ..).mul_left _

def hotspot := ∑ i∈s, base a^(d i) * LText W (s.erase i) p a x (x i) (Prelude.mark1 (W.surveys (d i)) (p i))
def basic := base a^(∑ i∈s,d i) * expo s (initial W (d:=d)) (fun i=>(road W p i).val) x
lemma exposure : basic W s p a x=hotspot W s p a x-∑ j:PlaqAxes,∑' u:Cover, sends (u,j) (sess W s p a x):=by
  unfold basic expo; rw [mul_sub, ← smul_eq_mul (a:=_ ) (b:= E _ _), ← map_smul (E _),stage1,map_sum]; congr 1; apply Finset.sum_congr rfl; intro i _; rw [map_smul, smul_mul_assoc,map_smul]; rfl
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; simp_rw [matching, tsum_mul_left]; rfl
lemma stroll (x y:Cover)(p:Stamp G):Trace.volume x (Trace.volume y p)=Trace.volume (x+y) p:=Chart2.same fun A=> by rw [ting,ting,ting,zone_add,add_comm y]
lemma snapshots (a:ℝ)(x y:Cover)(v:On.Grade G n):snaps W v (x+y) a= Trace.volume x (snaps W v y a):=by unfold snaps slack; rw [map_smul,stroll]
lemma stage_plus (y:Cover):sess W s p a (fun i=>y+x i)=Trace.volume y (sess W s p a x):=by unfold sess; rw [map_prod]; apply Finset.prod_congr rfl; intro i _; rw [snapshots]; exact (Mu.shifted _ _ 0).symm
lemma exposed (v: Cover)(p:Stamp G): E (Mu.root G) (Trace.volume v p)= E (Mu.root G) p:=by
  conv_lhs=> arg 2; rw [← came p]; skip
  rw [shifted _ _ p,← counts,scalar,ting,map_zero,counts,came]
lemma base_plus (y:Cover):baseZero W s p a (fun i=>y+x i)=baseZero W s p a x:=by rw [baseZero,baseZero,stage_plus, exposed]
lemma text_plus (y z:Cover) (v:Stamp G):LText W s p a (fun i=>y+x i) (y+z) v=LText W s p a x z v:=by
  change E (Mu.root G) (freeze (Trace.volume (y+z) v)*sess W s p a (fun i=>y+x i))=E (Mu.root G) (freeze (Trace.volume z v)*sess W s p a x); rw [stage_plus,← stroll,← shifted y _ v, ← map_mul (Trace.volume y),exposed]
lemma bill_plus (v y:Cover)(q:PlaqAxes): sends (v+y,q) (sess W s p a (fun i=>v+x i))= sends (y,q) (sess W s p a x):=by unfold sends; rw [stage_plus, show V3 G (v+y,q)=Trace.volume v (V3 G (y,q)) from ?_, ← map_mul, exposed]; rw [encoded (v+y), encoded y,stroll]
lemma whole_plus (y:Cover): basic W s p a (fun i=>y+x i)=basic W s p a x:=by
  rw [exposure W s p a (fun i=> y+x i),exposure W s p a x]; unfold hotspot; apply congr_arg₂ (·-·)
  · apply Finset.sum_congr rfl; intro i _; rw [text_plus];
  apply Finset.sum_congr rfl; intro i _; rw [← Equiv.tsum_eq (Equiv.addLeft y)]; apply tsum_congr; intro; apply bill_plus
end YM.XSpace.Foundation
