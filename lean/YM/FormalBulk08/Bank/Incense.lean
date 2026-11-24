import YM.FormalBulk08.Bank.Blue
import YM.AnalyticNext.QUARTIC_MATCH.Radius.Theme

/-! Noise byte in logs before evaluating graft/halo. `Ports` include cover
connectors; no n dependence. Proof imports radius Model and compiles for every
Choice; hence no frozen mask needed. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Bank
open Lava Gorge Shore Lattice Laurent Filter Function Lotus Orb Wick Reef Jets Series PowerSeries Stationary Wilson Next.Free
open Exterior Bloch RG Precision UVExtension.Free Work.F08 Flat Mesa Tree Work.F05
open AnalyticNext.QuarticMatch.Radius.Model
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n f : Side} (S : StepData n f) (P : Patch) (K : KernelChoices)

abbrev Ports (G : Gauge) := wire G (native P) ⊕ G.ColorIndex
def bet (x : Jets.Rays (Ports P G)) := (arm G (native P) 1 xfine) where xfine i := if lift i.1∈atEase P then x (Sum.inl i) else 0
@[simp] lemma bet_zero : bet P (0:Jets.Rays (Ports P G))=0:=by rw [bet,show bet.xfine P _=(0: Jets.Rays (wire G (native P))) from (by ext; simp [bet.xfine])]; exact map_zero _
def odds (x : Jets.Rays (Ports P G)) := G.lieExp (WithLp.toLp 2 fun i=>x (Sum.inr i))
def dice := Classical.choice (chooseable (marker P) (native P) (primary P K (marker P)))
def azure (i : Axis) (x : Jets.Rays (Ports P G)):= K.penalty * G.price (odds P x * ((primary P K (marker P)).prediction (represent (bet P x)) (dice P K) (stamp P i))⁻¹)
lemma azure_diff (h : P.Branches K G) (i) : ContDiffAt ℝ ω (azure P K (G:=G) i) 0:= by
   have hh: ContDiffAt ℝ ω (fun z:Jets.Rays (Ports P G)=> G.mat (odds P z)) 0:= by
      let f : Jets.Rays (Ports P G)→L[ℝ] G.Color := LinearMap.toContinuousLinearMap {toFun:=fun x=>WithLp.toLp 2 fun j=>x (Sum.inr j),map_smul':=fun _ _=> rfl, map_add':=fun _ _=> rfl}; exact G.exp_jet.contDiffAt.comp 0 f.contDiff.contDiffAt
   let t := primary P K (marker P); let c (x:Jets.Rays (Ports P G)) := t.prediction (represent (bet P x)) (dice P K) (stamp P i)
   have he : ContDiffAt ℝ ω (fun x=> G.mat (c x)) 0 := by
       apply ContDiffAt.comp (f:=bet P (G:=G)) (g:=fun v=>G.mat (t.prediction (represent v) (dice P K) (stamp P i))) _ _ _
       · rw [bet_zero]; exact Push.prediction_cont t h (stamp P i) (dice ..)
       refine (arm G (native P) 1).contDiff.contDiffAt.comp (f:=bet.xfine P) _ (contDiffAt_pi.mpr (fun j=>?_))
       unfold bet.xfine; split_ifs <;> first|exact contDiffAt_const|exact contDiffAt_apply ..
   refine ContDiffAt.mul contDiffAt_const (Work.F03.price_smooth (A:=fun x=>odds P x*(c x)⁻¹) ?_);simp_rw [G.mat_mul,G.mat_inv];exact hh.mul ((show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ he)

variable {P}
def drill (G : Gauge) (x : Site n) (i : Axis) : Ports S.patch G→ Glob G n f := Sum.elim (fun w=> Sum.inl (stretch S x (lift w.1),w.2)) (fun w=>Sum.inr (x,coord i,w))
def feet (G : Gauge) (P : Patch) (i : Axis) : Ports P G→Biglot (Board G P):= Sum.elim (fun w=> (Equiv.prodSumDistrib _ _ _).symm (Sum.inl (scroll P.L _ (lift w.1,w.2)))) (fun j=> (0,Sum.inr (coord i,j))) -- pipe issue
lemma tess (G : Gauge) (x : Site n) (i : Axis) : staging G S ∘ drill S G x i= tint x ∘ (Lotus.drip n) ∘ (feet G S.patch i):= by
   ext1 j; cases j with
   | inl w=>
      obtain ⟨h,u⟩:= spread_point S x (lift w.1)
      simp [staging,bifid,drill, Sum.elim, feet,h,u,split_co,Lotus.drip, boxCoord]; rw [add_comm]; rfl -- tree
   | inr w=> simp [drill,feet,staging,bifid,Lotus.tint,Lotus.drip]; rfl
lemma folded (x : Site n) (i : Axis) (z : Jets.Rays (Glob G n f)) :
    bet S.patch (z ∘ drill S G x i)=pick S x (frail z).2 := by
   ext ⟨j,v⟩ u; unfold bet AnalyticNext.QuarticMatch.Radius.Model.pick; simp_rw [ContinuousLinearMap.pi_apply]; split_ifs with hx <;> simp only [arm_apply,bet.xfine,hx,↓reduceIte];
   · rfl
   rfl
lemma azure_predict (j : Edge (Site n)) (h : S.patch.Branches S.kernel G) (t : S.Choices):
   ∀ᶠ z:Jets.Rays (Glob G n f) in 𝓝 0,S.kernel.penalty*G.price ((represent (frail z).1) j * (S.prediction (represent (frail z).2) t j)⁻¹)= azure S.patch S.kernel j.2 (z ∘ drill S G j.1 j.2) := by
   let ℱ (z:Jets.Rays (Glob G n f)) := pick S j.1 (frail z).2; let P:=S.patch; let A:=primary P S.kernel (marker P); let B:=dice P S.kernel
   have ht : Tendsto (fun z:Jets.Rays (Glob G n f)=> (frail z).2) (𝓝 0) (𝓝 0):=by simpa using! (frail_health (c:=n) (f:=f) (G:=G)).snd.continuousAt.tendsto -- implicit f
   have hb : Tendsto ℱ (𝓝 0) (𝓝 0):= by unfold ℱ;apply Tendsto.comp _ ht; simpa using (pick S j.1 (G:=G)).continuous.tendsto 0
   filter_upwards [ht.eventually (Push.lips S h j t),hb.eventually (Push.lips A h (stamp P j.2) B), hb.eventually (eventually_all.mpr (fun y:Site (marker P)=>Push.threshold A y))] with z hz hf hp
   unfold azure;rw [folded];change _=S.kernel.penalty * G.price (odds _ _ * (A.prediction (represent (ℱ z)) B (stamp P j.2))⁻¹); rw [Work.F03.represent_link, hz,hf];
   have he := (compiles S t h j (frail z).2 B hp).2
   have hu : Push.deck S j t.1 (frail z).2=Push.deck A (stamp P j.2) B.1 (ℱ z):=he
   simp only [Push.bonds]; rw [hu]; rfl
end YM.FormalBulk08.Bank
