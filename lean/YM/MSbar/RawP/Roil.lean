import YM.MSbar.RawP.Opus
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.RawP
open Function Filter Whisk Lis Measuring Cacao Aqua Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open AnalyticBridge.SectorAffine.Offset
variable {G:Gauge}{n:Side}{p k q:ℕ}{C B a:ℝ}{g f:Positions (Primary n G)→ℝ}{x: Positions (Primary n G)}{b:Primary n G}{L:List (Primary n G)}
local notation "W"=>Positions (Primary n G)
local notation "ψ"=>Measuring.chart n G
-- Ω.Free anchored derivative root uniform only. later to JetTab when needed. infinite sum.
structure Roil (f:Positions (Primary n G)→ℝ)(p:ℕ)(a:ℝ)(x:Positions (Primary n G))(C:ℝ): Prop where
    price: ContDiffAt ℝ p f x
    camp : 0≤C
    wallet (b: Primary n G)(T:List (Primary n G)) (h:T.length < p): |buoy f x (b::T)| ≤ C*raiseQ (Measuring.chart n G) a (b::T)
namespace Roil
lemma plus (h : Roil f p a x C)(ht:Roil g p a x B): Roil (fun x=>f x+g x) p a x (C+B):=by
    refine ⟨h.1.add ht.1,add_nonneg h.2 ht.2,fun b L hp=>?_⟩
    change |buoy (f+g) _ _|≤ _; rw [add_mul, show buoy (f+g) x (b::L)= buoy f x (b::L)+buoy g x (b::L) from Lis.addedL p _ f g h.1 ht.1 (by simp [hp])]; exact (abs_add_le ..).trans (add_le_add (h.3 b L hp) (ht.3 b L hp))
lemma scale (h:Roil f p a x C)(r:ℝ): Roil (fun x=>r*f x) p a x (|r| *C):=by
    refine ⟨h.1.const_smul r,mul_nonneg (abs_nonneg _) h.2,fun b L hp=>?_⟩; unfold buoy; rw [wed p _ _ _ h.1 (by simp [hp]),mul_assoc,abs_mul]; exact mul_le_mul_of_nonneg_left (h.3 b L hp) (abs_nonneg _)
lemma still (v:ℝ) : Roil (fun _ : W=>v) p a x 0:=by
    refine ⟨contDiffAt_const,le_rfl,fun b L hp=>?_⟩; unfold buoy; rw [fEntry (σ:=Primary n G) (k:=p) contDiffAt_const _ (by rw [List.length_cons]; omega), entry]; have hh:iteratedFDeriv ℝ (b::L).length (fun _ : W=>v) x=0:=by rw [iteratedFDeriv_const_of_ne (show (b::L).length≠0 from (by simp))];rfl
    rw [hh]; simp
lemma mono (h:Roil f p a x C)(he:C≤B):Roil f p a x B:= ⟨h.1,h.2.trans he,fun b L ht=>(h.wallet b L ht).trans (mul_le_mul_of_nonneg_right he (Real.exp_pos _|>.le))⟩
variable {ι:Type}[Fintype ι]
local notation "Y"=> ψ
lemma unite (f:ι→Positions (Primary n G)→ℝ)(t:ι→ℝ)(i:Finset ι)(h:∀ j∈i,Roil (f j) p a x (t j)): Roil (fun y=>∑ j∈i,f j y) p a x (∑ j∈i,t j):=by
    induction i using Finset.induction with|empty=> simp only [sum_empty]; exact still 0|insert a i he ih=> simp_rw [Finset.sum_insert he]; exact plus (h a (mem_insert_self ..)) (ih (fun j hj=>h j (mem_insert_of_mem hj)))
lemma stock (f:ι→Positions (Primary n G)→ℝ)(y:ι→Site n)(hy:∀ i:ι,ContDiffAt ℝ p (f i) x)(h:∀ i:ι,Beacon (Measuring.chart n G) (3*a) p (f i) (y i) x C)(hC:0 ≤ C)(ha:0 < a)(hq: Multiplicity y q): Roil (fun x=>∑ i:ι,f i x) p a x (C*(q*countCost a)):=by
    let T:= countCost a; have ht:=count_pos ha; refine ⟨ContDiffAt.sum (fun i _=> hy i),by positivity,fun b L hp=>?_⟩; let c:=raiseQ ψ a (b::L); have hh' :0≤ c:= (Real.exp_pos _|>.le); have hl:(b::L).length ≤p:=by rw [List.length_cons]; omega
    unfold buoy; rw [Lis.tot p _ _ f (fun i _=> hy i) (by simpa only [List.length_map])]; refine (Finset.abs_sum_le_sum_abs ..).trans ?_
    let g(i:ι):= Uniform.entry (f i) x ((b::L).get); calc
        _ ≤ ∑ i:ι,C*(Decay a (ψ b) (y i)* c):=by refine Finset.sum_le_sum fun i _=>?_ ; rw [fEntry (hy i) _ hl]; exact (h i _ hl _).trans (mul_le_mul_of_nonneg_left (ropeCost b L ha.le) hC)
        _ ≤ _:=by rw [←Finset.mul_sum,← Finset.sum_mul]; refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Multiplicity.count y hq ha (ψ b)) hh') hC).trans_eq (by ring)
end Roil
end YM.MSbar.RawP
