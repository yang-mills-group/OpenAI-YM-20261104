import YM.OPE.Compatible.Chain.Rock
/-!
# zero-fiber pseudo-inverse in Feynman gauge. All positive periods stamped. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Terp
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Matrix Score Libra Votive
open scoped Topology BigOperators ComplexConjugate Classical ContDiff
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Flume.Script
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent Further.FreeCovariance.KP
local notation "M" => TypeFace 1
abbrev ShellRow (C: KernelChoices) {r:ℕ}(v:Train r): Row M M:= Op C v
def spline (P:Row M M)(y:Momentum):Matrix M M ℂ:= P.read y+symbol 0 y*(symbol 0 y)ᴴ
def major (P:Row M M)(n:Side):Matrix (Body 1 n) (Body 1 n) ℝ:= P.acts n+grad n*(grad n)ᵀ
def slender (P:Row M M)(p:Site n): Matrix M M ℂ:= if p=0 then 0 else (spline P (mon p))⁻¹
def lineC (P:Row M M)(n:Side):= realOf (spectral (slender P (n:=n)))
lemma medic (P:Row M M)(hn:Whole P)(n:Side):approached (major P n)= spectral (fun p=> spline P (mon p)):= by
    have he : approached (P.acts n)= spectral (fun p=>P.read (mon p)):=by apply cancel_rotation; rw [spectral_read,circulant n P hn.safe]
    let Q:= grad n; rw [major,show approached (P.acts n+Q*Qᵀ)=_ from plus ..,he,prom_mul,prom_adj,show Q=grad n from rfl]; simp_rw [grad,d_spectral, spectral_adj, spectral_mul, spectral_add];rfl
where plus {α β : Type} (A B : Matrix α β ℝ) : approached (A+B)=approached A+approached B:= by ext; simp [approached]
variable {C:KernelChoices}{r:ℕ}
lemma spline_char (v:Train r)(h:4≤r)(p:Momentum)(hx:physical p): spline (ShellRow C v) p= outside ((pink C.penalty v).read p) (Exterior.q p):=by
   have hp:= (heart_heats C.penalty C.penalty_pos h (fun i:Train r=> i)).1.stock.whole v; let T:=Whole.boundary 1
   unfold spline ShellRow Op; rw [Whole.read (T.flipped.prod hp) T hx,T.flipped.read hp hx,read_opposite _ hx,reading]; rfl
lemma searchOn {p:Site n}(h:p≠0): lit n (lift p)∈search:=by
      let z:=lit n (lift p); have ht: mon p≠0:=by obtain ⟨i,hi⟩:=step_picks p h; intro hh; apply hi; rw [cell_step,hh]; simp
      refine ⟨fun i=>(local_price p i).trans_lt (by unfold earth; linarith [Real.pi_pos]),fun x=> ht ?_⟩; change z=0 at x; rw [show mon p=mcast z from (lit_mon ..).symm, x]; ext; simp [mcast]
lemma conduit (h:4 ≤ r)(v:Train r) {p:Site n}(hp:p≠0): IsUnit (spline (ShellRow C v) (mon p)).det:=by
      obtain ⟨a,b,c,ha,hc,h⟩:= Episode.paid C.penalty C.penalty_pos h
      obtain ⟨f,hv⟩:= h v; have hh:=tank_sealed ha hc f _ (searchOn hp); rw [spline_char v ‹4≤r› _ (real_frequency p)]
      unfold tank at hh; rw [Matrix.det_smul,Further.FreeCovariance.KP.fuel,tooth, hv,lit_mon] at hh; exact isUnit_of_mul_isUnit_right hh
lemma neutralize (n:Side)(h:4≤r)(v:Train r): major (ShellRow C v) n*lineC (ShellRow C v) n=1-missing n∧ lineC (ShellRow C v) n*major (ShellRow C v) n=1-missing n:=by
      let A:=ShellRow C v; have hh : Whole A:= Op_whole h v; unfold lineC; rw [←realOf_mul,←realOf_mul',medic _ hh, spectral_mul,spectral_mul]; let f: Site n→Matrix M M ℂ:=fun p=>if p=0 then 0 else 1
      have hf1(p:Site n): spline A (mon p)*slender A p=f p:= by
           by_cases hx:p=0
           · subst p;simp [slender,f]
           unfold f slender; rw [if_neg hx,if_neg hx]; exact Matrix.mul_nonsing_inv _ (conduit h v hx)
      have hf2(p:Site n): slender A p*spline A (mon p)=f p:= by
           by_cases hx:p=0
           · subst p; simp [slender,f]
           unfold f slender; rw [if_neg hx,if_neg hx]; exact Matrix.nonsing_inv_mul _ (conduit h v hx)
      change realOf (spectral (fun p:Site n=> spline A _ * slender A p))=_ ∧ realOf (spectral (fun p:Site n=> slender A p * spline A _))=_; simp_rw [hf1,hf2,and_self]; apply eq_sub_iff_add_eq.mpr
      unfold missing; rw [show realOf _+realOf _=_ from plus _ _, spectral_add]; rw [show (fun p=> f p+(if p=0 then 1 else 0))=fun _=>1 from funext fun i=>by by_cases h:i=0<;>simp [f,h], spectral_unit]
      ext i j; by_cases h:i=j<;>simp [realOf,Matrix.one_apply,h]
where plus {α : Type} (A B : Matrix α α ℂ): realOf A+realOf B=realOf (A+B) := by ext;simp [realOf]
end YM.OPE.Cascade.Terp
