import YM.FVAAlt2.First.Tent
import YM.SchemeConversionRG11.FirstW.Recal.Fund
/-!
# First-order only binding to PP.Reg `sap` calibration donor
 collects all factors real with COMPLEX tests applied; no first-order finite regulator bound claimed.
 Authority based on ACTUAL triangles. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.First.Portray
open Function Set Filter Finset Topology Lattice
open Precision Extra.FD Maxwell Labels Extraction Matrix
open FormalOPE FormalOPE.RG10.Gazebo FormalOPE.RG10.Position FormalOPE.RG10.Carryon
open Pert Pert.Position PertExtension PertExtension.LatticePT PertExtension.Position PertExtension.Physical
open PertExtension.Position.Triangle
open Home Home.Subsidy Tent SchemeConversionRG11
open RG10 (Through)
open PowerSeries (C coeff constantCoeff)
open scoped BigOperators Classical Topology PowerSeries Matrix
variable {G:Gauge}{F:Frames G}{d k m:ℕ}
local notation "V"=> RG10.Position.Deck F d
local notation "K"=> deck F d
local notation "L"=> Maxwell.freeTable F
local notation "Ω"=> constantCoeff (R:=ℝ)
-- Encode, using REAL coefficients (not ℂ). First donor converges on actual tests. Even complex tests projected.
variable (B:Issue F d)
def loot (p:Datum V): fps:= PowerSeries.mk fun i=> ( B p.fst.n p.fst.test i ( ⇑(deck F d) ∘ p.2 ) ).re
variable {I J:Type*}[Fintype I][Fintype J][DecidableEq I]
-- copy lemma from RG10/Gazebo/Entries (private)
private lemma leak {I J:Type*}[Fintype I][Fintype J][DecidableEq I]
 (a:I→J)(f:I→J→ℝ)(g:(I→J)→ℝ) (i:I): ∑ p : I→J, g p * (f i (p i) * ∏ j∈ univ.erase i, Physical.diag J (a j) (p j)) = ∑ u:J,g (update a i u) * f i u := by
 let x(u:J):= update a i u; have hx:Injective x:= fun j k hk=> by simpa [x] using congr_fun hk i
 let G(p:I→J):= g p * (f i (p i)*∏ j∈univ.erase i,Physical.diag J (a j) (p j))
 change ∑ p:I→J,G p=_
 rw [← sum_subset (f:=G) (subset_univ (Finset.image x univ)) ?_, sum_image hx.injOn]
 · apply sum_congr rfl; intro j _; unfold G x; rw [update_self,prod_eq_one,mul_one]
   intro k hk; simp [Physical.diag,update_of_ne ((mem_erase.mp hk).1)]
 intro p hp hy
 have he:∃ j,j≠i ∧ a j≠p j:= by
   by_contra! ht; exact hy (mem_image.mpr ⟨p i,mem_univ _,funext fun j=>by unfold x; by_cases h:j=i; subst j; simp; rw [update_of_ne h,ht j h]⟩)
 obtain ⟨j,hj,hh⟩:=he; unfold G; rw [Finset.prod_eq_zero (mem_erase.mpr ⟨hj,mem_univ _⟩) (by simp [Physical.diag,hh]),mul_zero, mul_zero]
-- matrix import definitions. θ parity
local notation "σι"=> Mark V PertExtension.Physical.Profile.n
local notation "M"=> Matrix V V fps
local notation "P"=> PertExtension.Physical.Profile.n
abbrev charge (W:FrameAt V ℝ): M:= Matrix.of (RG10.Gazebo.pulse W)
-- exact at regulator as leading identity + tangent 
lemma charge_zero (W:FrameAt V ℝ): (charge W).map Ω=(1: Matrix V V ℝ):= by rw [RG10.Carryon.diag_one]; ext i j; simp [charge,RG10.Gazebo.pulse]
lemma charge_1 (W: FrameAt V ℝ): Stg (charge W) 1= Matrix.of W:=by ext i j; by_cases h:i=j <;> simp [h,charge,RG10.Gazebo.pulse,Stg]
lemma charge_Up (W:tents F d) : Upright (charge W.val):=by
 apply Upright.obtainable
 · rw [ show Stg (charge W.val) 0=1 from by rw [←charge_zero W.val]; ext i j; simp [Stg], sub_self ]; exact Submodule.zero_mem _
 intro i hi; by_cases he:i=1; · rw [he,charge_1]; exact W.property
 rw [ show Stg (charge W.val) i=0 from ?_ ]; exact Submodule.zero_mem _
 ext a b; by_cases hx:a=b <;> simp [hx,charge, RG10.Gazebo.pulse,Stg,PowerSeries.coeff_X,hi.ne',he] -- inspect
lemma zero_id (A: V → V→ℝ) (F: Datum V→fps) (p: Datum V): coeff 0 (mix F (charge A) p)= coeff 0 (F p):= by simp_rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact congr_fun ( show Ω ∘ mix F (charge A)=(Ω ∘ F) by rw [mixPap, charge_zero,mix1]) p
lemma firstDiag(A:V→V→ℝ)(W:Datum V→fps)(v:Datum V) : coeff 1 (mix W (charge A) v ) = coeff 1 (W v)+ ∑ i:Fin v.1.n,∑ j:V, constantCoeff (W ⟨v.1,update v.2 i j⟩)* A (v.2 i) j:=by
 let Z(i j):= (charge A i j); let E:=Fin v.1.n;
 unfold mix; simp_rw [map_sum,PowerSeries.coeff_one_mul,map_prod,sum_add_distrib];
 have hx : coeff 1 (W (⟨ v.1,v.snd ⟩:Datum V))=(∑ u:E→ V, coeff 1 (W (⟨v.1,u⟩:Datum V))*∏ i:E, Ω (charge A (v.2 i) (u i))):= Eq.symm ( show mix ((coeff 1) ∘ W) ((charge A).map Ω) v= _ from congr_fun (show mix _ _= _ from Eq.trans (congr_arg _ (charge_zero A)) (mix1 ..)) v ) -- HP
 congr 1; exact hx.symm
 have ht(f:Fin v.fst.n→fps)(x:fps): coeff 1 (∏ i:Fin v.fst.n,f i)*constantCoeff x=∑ i:Fin v.fst.n,constantCoeff x*(coeff 1 (f i)*∏ j∈univ.erase i,Ω (f j)):=by rw [← Finset.mul_sum, mul_comm _ (Ω _), show coeff 1 _ =_ from Pert.First.first_product f univ]; rfl
 simp_rw [ht]; rw [sum_comm]; apply Finset.sum_congr rfl; intro i _
 have ha(i j:V): Ω (charge A i j)=Physical.diag (V) i j:= by rw [charge,of_apply]; simp only [RG10.Gazebo.pulse,map_add,map_mul, PowerSeries.constantCoeff_X,PowerSeries.constantCoeff_C,mul_zero,add_zero ]
 simp_rw [ show ∀ i j, coeff (R:=ℝ) 1 (charge A i j)=A i j from congr_fun₂ ( charge_1 A ), ha ]; exact leak v.2 (fun i j=> A (v.2 i) j) (fun p=> constantCoeff (W ⟨v.1,p⟩)) i
variable (b :ℕ→ Buffer F d)(H: tents F d)(H0:b 0=0)(H1: b 1= buf H)
include H0 H1
lemma imprint_id (p : Datum V): Through 1 ( mix (loot B) (charge H.val) p ) ( loot (Issue.imprint b B) p ) := by
 intro i hi; interval_cases i; · rw [zero_id, loot,loot,PowerSeries.coeff_mk, PowerSeries.coeff_mk ]; rw [show Issue.imprint b B p.1.n p.fst.test 0=B p.1.n p.fst.test 0 from ?_ ]; unfold Issue.imprint Tape.hinge; rw [Series.liftJet_zero]; change Tape.put (b 0) _ = _; rw [H0,Tape.put_zero];rfl
 rw [firstDiag]; simp_rw [loot, PowerSeries.coeff_mk, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk];
 let v:= K ∘ p.2; let n:= p.1.n; let T:=B p.fst.n p.fst.test; let a:= RG10.Position.deck F d
 rw [Issue.imprint, Tape.leading _ _ H0]; simp only [ContinuousMultilinearMap.add_apply,Tape.vary_at,H1,Complex.add_re,Complex.re_sum]; rw [add_comm _ (∑ _ ,_) ]; congr 1; apply Finset.sum_congr rfl; intro i _; change _=( T 0 (update v i ((buf H).val (a (p.2 i)) )) ).re; rw [ buf_at,show T 0 (update v i (∑ j:V, H.val (p.2 i) j • K j))= _ from ( T 0 ).toMultilinearMap.map_update_sum univ i _ _, Complex.re_sum ]; apply Finset.sum_congr rfl; intro j _; rw [ MultilinearMap.map_update_smul,Complex.smul_re ]; change _=H.val _ _* (T 0 _).re; rw [mul_comm]; congr 3; ext r : 1; by_cases he:r=i <;> simp [he,Function.update,v,a]
end YM.FVAAlt2.First.Portray
