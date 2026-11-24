import YM.FormalOPE.RG10.MarkovChain.Vault
/-!
 # Single-slot multiplicative packets for the Jacobian; dependence only on one slice
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.MarkovChain
open Function Filter Topology Set MeasureTheory PertExtension Precision
open Inherit Push.Loops Chart Lattice RG GaussianScore PowerSeries
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric
open Papers Warp Line Roof
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G: Gauge} {c f n: Side}
variable {S:StepData c f} {H:S.patch.Branches S.kernel G}{t:S.Choices}{hf:_root_.Even f.val}{L:Fabric G c} {C:Cloth L}{P:Inside S.ratio}
local notation "T0"=> Cloth.inLayer (t:=t) (b:=H) (h:=hf) P C
local notation "d"=> Pathway (S:=S) (H:=H) (t:=t) (hf:=hf) (C:=C) (P:=P)
 def Atlas : Index S P ⊕ C.choose.Bulk ≃ (T0).choose.Bulk:= indSpace S H t hf L P C.choose
local notation "cR"=> Atlas (t:=t) (H:=H) (P:=P) (C:=C) (hf:=hf)
@[simp] lemma fast_slot (x:Cross (G:=G) S P)(y:Field C.choose)(i:Index S P): d (x,y) (cR (.inl i)) = x i:= rfl
@[simp] lemma tail_slot (x:Cross (G:=G) S P)(y:Field C.choose)(i:C.choose.Bulk): d (x,y) (cR (.inr i))= y i:= rfl
namespace Vault
lemma fromFixed {n:Side}{L:Fabric G n}{T:Cloth L}(x:PowerSeries ℝ): Vault T (carry x):= by
 cases T with
 | floor=> trivial
 | @inLayer c f S H t hf L P C=>
   rw [Vault]; let D:= Pathway (H:=H) (t:=t) (hf:=hf) (P:=P) (C:=C); refine ⟨fun _ _ _ _=>by simp,?_⟩
   rw [show boost (coarse D) (carry x)=carry x from by apply into; intro v; simp only [caught,load]]
   exact fromFixed (T:=C) x
termination_by structural T
variable {L':Fabric G n}{T:Cloth L'}
lemma identity : Vault T 1:= by simpa only [_root_.map_one] using fromFixed (T:=T) (1:PowerSeries ℝ)
lemma prod {α:Type}(V:α→Ticket (Field T.choose))(s:Finset α)(h:∀ i∈s, Vault T (V i)): Vault T (∏ i∈s,V i):= by
 induction s using Finset.induction with
 | empty=> rw [Finset.prod_empty]; exact identity
 | insert i s hq ih=> rw [Finset.prod_insert hq]; exact Vault.mul (h i (by simp)) (ih (fun i hi=> h i (by simp [hi])))

variable (E:Ticket G.Color)
 def perm {L:Fabric G n}(T:Cloth L)(i:T.choose.Bulk): Field T.choose→ₗ[ℝ] G.Color:= LinearMap.proj i
lemma permanently {n:Side}{L:Fabric G n}(T:Cloth L)(i:T.choose.Bulk): Vault T (boost (perm T i) E):= by
 cases T with
 | floor => trivial
 | @inLayer c f S H t hf L P C=>
   let D:= Pathway (H:=H) (t:=t) (hf:=hf) (P:=P) (C:=C); let J:= Atlas (H:=H) (t:=t) (hf:=hf) (P:=P) (C:=C)
   obtain ⟨u,rfl⟩:= J.surjective i
   cases u with
   | inl i=>
     rw [Vault]; refine ⟨fun _ _ _ _=>?_,?_⟩
     · simp only [caught]; rfl
     rw [show boost (coarse D) (boost (perm (Cloth.inLayer (t:=t) (b:=H) (h:=hf) P C) (J (.inl i))) E)= carry (Stack.read 0 E) from by apply into; intro v; simp only [caught, load]; rfl]
     exact fromFixed _
   | inr i=>
     rw [Vault]; refine ⟨fun x y z _=>?_,?_⟩
     · simp only [caught]; exact mul_comm (Stack.read (y i) E) (Stack.read (z i) E)
     rw [show boost (coarse D) (boost (perm (Cloth.inLayer (t:=t) (b:=H) (h:=hf) P C) (J (.inr i))) E)= boost (perm C i) E from by apply into; intro v; simp only [caught]; rfl]
     exact permanently C i -- E implicit?
termination_by structural T
section
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
lemma climbing {U:E→ℝ}(a:F→ₗ[ℝ] E)(h:ContDiffAt ℝ ∞ U 0) : boost a (rise U)=rise (U∘a):= by
 have hh: ContDiffAt ℝ ∞ (U∘a) 0:= (show ContDiffAt ℝ ∞ U (a 0) from by simpa only [map_zero] using h).comp 0 ((LinearMap.toContinuousLinearMap a).contDiff.contDiffAt) -- check
 apply into; intro x; rw [caught]
 apply PowerSeries.ext; intro n; rw [read_rise,read_rise]
 have hreal: (fun s:ℝ=> U (s • a x))= (fun s:ℝ=>(U∘a) (s • x)):=funext fun s=> by simp
 have he:= directions h (a x); rw [hreal] at he
 exact congr_fun (he.unique (directions hh x)) _
end
variable {J:ChartRatio G} (Hj:LocalRatio J)
include Hj in
lemma charge : Vault T (rise (jacobian J)):= by
 let Q : T.choose.Bulk → Field T.choose→ℝ:= fun i=> fee J ∘ perm T i
 have he i: ContDiffAt ℝ ∞ (Q i) 0:= (show ContDiffAt ℝ ∞ (fee J) ((perm T i) 0) from by rw [map_zero]; exact (Ratio.fee_smooth Hj).of_le le_top).comp 0 ((LinearMap.toContinuousLinearMap (perm T i)).contDiff.contDiffAt)
 have hf (s: Finset T.choose.Bulk): Vault T (rise (∏ i∈s,Q i)):= by
    induction s using Finset.induction with
    | empty=> rw [Finset.prod_empty, rise_one]; exact identity
    | insert i s h ih=>
      rw [Finset.prod_insert h,rise_mul (he i) (show ContDiffAt ℝ ∞ _ _ from ?_)]
      · refine Vault.mul ?_ ih; dsimp only [Q]; rw [←climbing (perm T i) ((Ratio.fee_smooth Hj).of_le le_top)]; exact permanently (rise (fee J)) _ _
      first| exact contDiffAt_prod (fun i _=>he i)| exact contDiffAt_prod' (fun i _=>he i)
 rw [show jacobian (U:=T.choose.Bulk) J= ∏ i,Q i from funext fun i=> by simp only [jacobian,Finset.prod_apply,Q]; rfl]; exact hf _
end Vault
end YM.FormalOPE.RG10.MarkovChain
