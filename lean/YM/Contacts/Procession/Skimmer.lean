import YM.Contacts.Procession.Laptop
/-! # Interior motion of principal Mark shells. Canonical A0 filter realizes all moments for Peek.T.Stored budget permit separate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Procession.Pierian
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Sun Xenon Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Welcome Resetter Shuttle.Tide
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
open Tree FreeResolvent Draw PhysicalNext.RankCovariance Catch Hinges Lotus Welcome.Theater
open Barrage Barrage.Slope Barrage.Reserve Barrage.Reserve.Oasis Odor Odor.Winding Odor.Winding.Sales Port
open Planned.PrimaryIntegral295 Carrier Place MultiNext.SignedSource Pattern Shuttle.Tide.Morning
open Tensor Mediator Next.Foundations Labels Source Drops WardBin Cartons Broadcast
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
variable {G:Gauge}{n k i r l p j d h u:ℕ}{b c :ℝ}{X ι E W: Type}[NormedAddCommGroup E] [NormedSpace ℝ E][NormedAddCommGroup W][NormedSpace ℝ W]
section
variable {f:E→W}{v:Fin k→ E}{P:Tensor.T W ℝ k} [FiniteDimensional ℝ W]
lemma pureD (P:Tensor.T W ℝ k) (hi:n<k) : iteratedFDeriv ℝ n (Tensor.diagonal P) 0=0:= by
    suffices A:Tensor.coeff (Tensor.diagonal P) n 0=0 by unfold Tensor.coeff at A; exact (smul_eq_zero.mp A).resolve_left (by positivity)
    refine Tensor.ext_diag _ _ (Tensor.coeff_symm (Tensor.diag_smooth ..|>.contDiffAt)) (fun _ _=>rfl) (funext fun x=>?_) ; change Radial.jet _ n x =0; rw [Milling.radiant (Tensor.diag_smooth P ω|>.contDiffAt.analyticAt) k n (fun x t=>Tensor.homogeneous P x t) x,if_neg (Nat.ne_of_lt hi)] -- args
lemma mainD (P: Tensor.T W ℝ k) (h:Tensor.Sym P): Tensor.coeff (Tensor.diagonal P) k 0=P:= by refine Tensor.ext_diag _ _ (Tensor.coeff_symm (Tensor.diag_smooth ..|>.contDiffAt)) h (funext fun x=>?_); change Radial.jet _ k x= _; exact (Milling.radiant (Tensor.diag_smooth P ω|>.contDiffAt.analyticAt) k k (fun x t=>Tensor.homogeneous P x t) x).trans (if_pos rfl)
lemma pure_chain (h:ContDiffAt ℝ ω f 0)(hx:f 0=0)(hp: Tensor.Sym P) : Tensor.coeff (Tensor.diagonal P ∘ f) k 0 v=P (fun i=>fderiv ℝ f 0 (v i)):= by
    unfold Tensor.coeff; simp only [_root_.smul_apply]; rw [iteratedFDeriv_comp (Tensor.diag_smooth P ω|>.contDiffAt) h (show (k:WithTop ℕ∞)≤ω from le_top),FormalMultilinearSeries.taylorComp,_root_.sum_apply, Finset.sum_eq_single (OrderedFinpartition.atomic k)]; swap
    · intro i hi he; change (iteratedFDeriv ℝ i.length _ (f 0)) _=0; rw [hx,pureD P (lt_of_le_of_ne i.length_le (fun ht=>he (Stationary.allSingle i ht)))]; rfl
    swap; · simp
    let p:= OrderedFinpartition.atomic k; let X i:= iteratedFDeriv ℝ (p.partSize i) f 0 (v ∘ p.emb i); have he (i): X i = fderiv ℝ f 0 (v i):= by unfold X; change (iteratedFDeriv ℝ 1 f 0) _ = _; rw [iteratedFDeriv_one_apply]; rfl -- casts
    change ((k.factorial:ℝ)⁻¹) * ((iteratedFDeriv ℝ k (Tensor.diagonal P) (f 0)) X)=_; rw [hx]; exact (DFunLike.congr_fun (mainD P hp) X).trans (congr_arg P (funext he))
end
section price
-- dictionary representation in thermal visual samples. Carries all charges. For this Slot only the order diagonal chart read matters.
abbrev pso (G:Gauge)(d k:ℕ):= Cartons.bins G d k
local notation "T_" => (d*(d+1))
def subcode (X:Tensor.T (Ship G T_) ℝ k): pso G d k:= Pi.single (Fin.last k) X
def cursor (B:Labels.Frame G d)(j k:ℕ)(Y: Field (Fin k) (Node (Dye G))) := Cartons.peek B j k (subcode (Shuttle.sheet k Y (Tide.lens G T_)))
lemma cut_axis (X:Tensor.T (Ship G T_) ℝ k): Cartons.dollar (subcode X)= Tensor.diagonal X ∘ Cartons.costume (G:=G) d T_ := by
   funext y; unfold dollar; rw [Finset.sum_eq_single (Fin.last k)]; exact congr_arg (fun F:Tensor.T (Ship G T_) ℝ k=> Tensor.diagonal F _) (Pi.single_eq_same ..); · intro i hi he; rw [subcode,Pi.single_eq_of_ne he]; rfl
   simp
abbrev glyph (v:Board G d):= generation (WardBin.key v)
lemma track (p:Board G d) (he: d≤u) (hp:glyph p ≤d) : fderiv ℝ (costume (G:=G) d u) 0 (WardBin.chip p) ∈ Draws G u (glyph p):= by
    let X:= Snap G d; let A:= Draft G d; let v:= (Morning.plank G d) (WardBin.chip p); let s:=glyph p; have hs:s=p.1.val+2:= rfl; have hm:1≤ s:=(by omega); have hy:v∈Jar G d s:= ⟨ by change glow G.Color d 0∈_; rw [map_zero]; apply Submodule.zero_mem, fun i hi=> Pi.single_eq_of_ne (show i≠p.1 by intro h; rw [h] at hi; omega) _⟩
    have ht:=rain_health (G:=G) he 1 (by norm_num) (fun _=>s) (fun _ => v) ⟨fun i=> ⟨hm,hy⟩,by simpa using hp⟩; unfold costume; rw [fderiv_comp]; · rw [ (Morning.plank G d).map_zero,(Morning.plank G d).fderiv]; change fderiv ℝ (rain G d u) 0 v ∈ Draws G u s; simpa only [sum_const,card_univ,Fintype.card_fin,one_smul,iteratedFDeriv_one_apply] using ht
    · rw [ (Morning.plank G d).map_zero]; exact (germ_rain ..).differentiableAt (by simp)
    exact (Morning.plank G d).differentiableAt
lemma design_leg {U: Ship G T_}(h:U∈ Draws G T_ i)(hq:i≤d)(h₀: 0 < i ): ∃ p∈ Place.rangeLt (Axis→G.Color) i, (fun u:Node (Dye G)=> lens G (d*(d+1)) u U)=sense (G:=G) p:= by
    choose F h H using (show ∀ i':Axis, ∃ f:E4→ G.Color, f ∈ Powers.space E4 G.Color (i-1) ∧ U i'=fit (d*(d+1)) f from h); apply (quarter (n:=i) _ h₀).2; refine ⟨F,h,fun z a i=>?_ ⟩ ; rw [Tide.glaze_at,H]; apply congr_arg (fun t:G.Color=>t i); exact congr_fun (Tide.sky (Powers.widen _ _ ((Nat.sub_le ..).trans (le_trans hq (le_mul_of_one_le_right (by omega) (by omega)))) (h a))) _ -- inspect
-- input payment.Rank-poly all pixels.
def Remains (h:ℕ) (v: Field (Fin k) (Node (Dye G))):Prop:= ∀ f:Fin k→ plate G,∀ n:Fin k → ℕ,(∀ i,1≤ n i) → (∀ i,f i∈ Place.rangeLt (Axis → G.Color) (n i)) → ∑ i,n i ≤ h → say v (fun i=> sense (G:=G) (f i))=0
end price
end YM.Contacts.Procession.Pierian
