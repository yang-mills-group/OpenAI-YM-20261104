import YM.FormalBulk08.Spigot.Sidelight
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Spigot
open Function Filter Lattice RG Laurent Bloch Exterior Wilson
open Reef Lava Gorge Mesa Shore Lotus Orb Wick Series Jets PowerSeries North Cork City Wine Flat Glide Bank Chapel Rift Kemp Dawn MeasureTheory
open Stationary hiding shine Rays
open scoped Topology ENNReal Matrix BigOperators Classical ContDiff
variable {I:Type*}{G:Gauge}{n:Side}{r t u e E D:ℕ}{A B C σ η:ℝ}
open Grail Precision Work.F03 Pose Tensor
open Planned.PrimaryIntegral295 Place Carrier
open scoped Matrix.Norms.Frobenius

lemma sum_rails (f:chain (Biglot I) r→ℝ)(o:I)[Fintype I] (h:C≥0)(H:∀ i, f i ≤ Real.exp (-η * herb (fame _) (0,o) i)*C)(hp:∀ i,0≤f i)(he:0<η):SumBudget f ((∑' i:chain (Biglot I) r,Real.exp (-η * herb (fame _) (0,o) i))*C):= sum_tier ⟨fun _=>mul_nonneg (Real.exp_pos _).le h,(harvest o he).mul_right _,le_of_eq (tsum_mul_right ..)⟩ hp H

lemma tincture (G:Gauge)(r:ℕ)(v:chain (hue G) r): (fun i=>picker G r i v)∈ paints G r:= by
    have he:=picks (Pi.single v 1)
    rwa [show picker G r *ᵥ Pi.single v 1=(fun i=>picker G r i v) from (Matrix.mulVec_single ..).trans (funext fun i=>by simp)] at he
lemma budget_sigma {X:Type*}{Y:X→Type*}[∀ x,Fintype (Y x)]{f:(Σ x,Y x)→ℝ}(h:∀ x,0≤f x) (he:SumBudget (fun x=>∑ j:Y x,f ⟨x,j⟩) A): SumBudget f A := by
    rw [show (fun x=>∑ j:Y x,f ⟨x,j⟩)=(fun x=>∑' j:Y x,f ⟨x,j⟩) from funext fun i=>(tsum_fintype _).symm] at he; let hp:= (summable_sigma_of_nonneg h).mpr (And.intro (fun _=> .of_finite) he.2.1); exact ⟨h,hp,hp.tsum_sigma.trans_le he.2.2⟩
lemma budget_fan {X Z:Type*}[Fintype Z]{f:X×Z→ℝ}(h:∀ x,0≤f x)(he:SumBudget (fun x=>∑ j:Z,f (x,j)) A): SumBudget f A:= by
    let V: (Σ _x:X,Z) ≃ X×Z := Equiv.sigmaEquivProd X Z
    have H:= budget_sigma (X:=X) (Y:=fun _=>Z) (f:= f ∘ V) (fun x=>h _) he; exact ⟨h,V.summable_iff.mp H.2.1,(Equiv.tsum_eq V f).symm.trans_le H.2.2⟩
namespace Dill
variable (P:Dill) (R:Herald)
abbrev Foils (G:Gauge)(r:ℕ):= P.Compass r × chain (hue G) r
def chamber (i:P.Foils G r): Atom G r where
    leg u:=R.path (P.fable i.1 u).2
    coeff x:= picker G r x i.2
def shutter (i:P.Foils G r)(T:Tile (edgeL G) r):= (P.oracle R i.1 T).coeff i.2
lemma shut_abs (i:P.Foils G r)(T:Tile (edgeL G) r):|shutter P R i T|=|T (arctic G r (i.1.1,i.2))|:= by unfold shutter oracle; simp_rw [abs_mul,Finset.abs_prod,show ∀ j:Fin r,|(P.fable i.1 j).1|=1 from fun j=> (P.pos (i.1.1 j) _).1,Finset.prod_const_one,mul_one]
lemma chamber_mag (i:P.Foils G r): (chamber P R i).magnitude≤ reserve (picker G r):= by
    unfold Atom.magnitude reserve; refine Finset.sum_le_sum fun k _=>?_ ; exact Finset.single_le_sum (f:=fun j=>‖picker G r k j‖) (fun i _=>norm_nonneg _) (Finset.mem_univ i.2)
lemma chamber_head (p:P.Foils G r): (chamber P R p).Invariant:= tincture G r p.2
lemma chamber_size (p:P.Compass r)(T:Tile (edgeL G) r)(H:Lust T)(U:Link G n): traceP U (PowerSeries.coeff r (paste (spring (P.oracle R p T))))=∑ i:chain (hue G) r, P.shutter R (p,i) T * traceP U (PowerSeries.coeff r (paste (spring (P.chamber R (p,i))))):= by
    simp_rw [springPin]; let a:=P.oracle R p T
    have ha : a.coeff∈paints G r:= oracle_invar P R p T H
    let M(v:Ink G r):= ∏ j,faceCurl (slotFace (a.leg j) 0) (Stationary.arm _ _ _ U) (v j)
    change (∑ x,a.coeff x*M x) = ∑ i:Ink G r,a.coeff i * ∑ x,picker G r x i * M x
    simp_rw [Finset.mul_sum, ←mul_assoc]; rw [Finset.sum_comm (s:=(Finset.univ:Finset (Ink G r))) (f:=fun i x=> a.coeff i*picker G r x i*_)]; apply Finset.sum_congr rfl; intro i _; rw [←Finset.sum_mul]; congr 1
    have he:=congr_fun (keeps _ ha) i; symm; apply Eq.trans ?_ he; apply Finset.sum_congr rfl; intro j _; exact mul_comm ..
lemma foil_card (o:Loc G 1)(t:chain Stoop r)(x:chain (hue G) r):(Fintype.card (P.Hats t):ℝ) ≤ (4:ℝ)^r * (1+ herb (fame _) (0,o) (arctic G r (t,x)))^r:= by
    rw [←mul_pow]; let D:ℝ:= herb (fame _) (0,o) (arctic G r (t,x))
    have ht : Fintype.card (P.Hats t)=∏ i,P.n (t i):= by rw [Fintype.card_pi]; simp
    rw [ht,Nat.cast_prod]; refine le_trans (Finset.prod_le_prod (g:= fun _=>4*(1+D)) (fun _ _=>Nat.cast_nonneg _) (fun i _=>?_)) ?_; swap
    · simp [D]
    have he: size (t i).1≤ herb (fame _) (0,o) (arctic G r (t,x)):= Pose.seat_ink o (arctic G r (t,x)) i; have hx : (P.n (t i):ℝ) ≤ 4*D:= by unfold D; exact_mod_cast (le_trans (P.cap _) (Nat.mul_le_mul_left 4 he))
    linarith
end Dill
end YM.FormalBulk08.Spigot
