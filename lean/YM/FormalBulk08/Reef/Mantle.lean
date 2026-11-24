import YM.FormalBulk08.Reef.Feast

/-! Ward witnesses and axis translations, including sliced repoking. These
Gauge identities are used in formal g algebra only. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Reef
open Series Wick Jets Orb Matrix Filter Set Precision Work.F05 RG Wilson Lattice Tree MeasureTheory Function
open Stationary hiding Rays
open scoped BigOperators ContDiff Topology Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f n : Side} {S : StepData c f} {I : Type} [Fintype I]

/-- Perturbative Ward under local log-coordinate charts/gauge germs, *constant* gauge allowed at origin. -/
def Rite (W T : Pap (wire G n)) (s : Signed) (x : Site n) := ∀ (I : Type) [Fintype I]
    (a b : Rays I→Rays (wire G n)) (k : Rays I→ Site n → G.El), a 0=0 → b 0=0 → ContDiffAt ℝ ω a 0 → ContDiffAt ℝ ω b 0 → Army k 0 → (∃ g:G.El,k 0=fun _=>g) →
      (∀ᶠ z in 𝓝 0,input G n (b z)=Lattice.gauge (k z) (pull s x (input G n (a z)))) → roam ℝ (motor a) W=roam ℝ (motor b) T

def Civic (W : Pap (wire G n)) := ∀ s x,Rite W W s x
variable (F : Forest S.ratio) (s : Signed) (s' : Site c) (k : Rays I→ Site c→G.El) (hp : Army k 0) (H : ∃ g:G.El,k 0=fun _=>g)

def ladenF (x : Rays I) := k x ∘ S.ratio.parent
def swivel (x : Rays I) := pans S F s s' (ladenF (S:=S) k x)
def winged (x : Rays (Pine G S F⊕I)) := offer G F (x ∘ Sum.inl)
def rawcut (z : Rays (Pine G S F⊕I)) := cook S s s' (ladenF (S:=S) k (z ∘ Sum.inr)) (input G f (winged F z))
def scheme (z : Rays (Pine G S F⊕I)) := F.foldAt (rawcut F s s' k z) * ladenF (S:=S) k (z ∘ Sum.inr)
def preserveW (z : Rays (Pine G S F⊕I)) := Profiles.wick F (rawcut F s s' k z)
def orbitY (z : Rays (Pine G S F⊕I)) := (stand G F).symm (fun i : F.Free=> plogC G (preserveW F s s' k z i))

lemma wing_service : ContDiffAt ℝ ω (@winged G _ _ _ I F) 0 := (offer G F).contDiff.contDiffAt.comp (f:=fun z=> z ∘ Sum.inl) _ (contDiffAt_pi.mpr fun _=>contDiffAt_apply ..)
include hp
lemma livery : Army (fun z:Rays (Pine G S F⊕I)=> ladenF (S:=S) k (z ∘ Sum.inr)) 0 := by
    intro i; let R:=fun z:Rays (Pine G S F⊕I)=>z ∘ Sum.inr; exact (hp (S.ratio.parent i)).comp (f:=R) (0: Rays (Pine G S F⊕I)) (contDiffAt_pi.mpr fun _=>contDiffAt_apply ..)
lemma cutting : Army (rawcut F s s' k) 0 := by
    have ht : Army (fun z:Rays (Pine G S F⊕I)=>pull s (S.ratio.embed s') (input G f (winged F z))) 0 := by
       have hh : Army (fun z:Rays (Pine G S F⊕I)=> input G f (winged F z)) 0:=Army.powL (wing_service F)
       intro i; simp only [pull,Step.read]; split
       · exact hh.inv _
       exact hh _
    exact (livery F k hp).slant ht
lemma skint : Army (scheme F s s' k) 0 := (drape_lit S F (W:=rawcut F s s' k) (cutting F s s' k hp)).mul (livery F k hp)
lemma plump : Army (preserveW F s s' k) 0 := by
   have ht:= cutting F s s' k hp; intro i; exact ((drape_lit S F ht).slant ht) i.val
include H
omit hp [Fintype I] in
lemma stillcut : rawcut F s s' k 0=1 := by
   obtain ⟨g,h⟩:=H; funext i; simp [rawcut,winged, cook,ladenF,h, Lattice.gauge,pull,Step.read, show ((0:Rays (Pine G S F⊕I)) ∘ Sum.inl)=0 from rfl,show ((0:Rays (Pine G S F⊕I)) ∘ Sum.inr)=0 from rfl]
omit hp [Fintype I] in
lemma equality_home : ∃ g:G.El,scheme F s s' k 0=fun _=>g := by
   rw [scheme,stillcut F s s' k H]; obtain ⟨g,h⟩:=H; refine ⟨g,?_⟩;funext i
   change F.foldAt (1:Config G f) i * k 0 _=g;rw [h]; simp [Forest.foldAt]
omit hp [Fintype I] in
lemma home_base : preserveW F s s' k 0=1 := by
   rw [preserveW,stillcut F s s' k H];ext i;simp [Profiles.wick,Profiles.wiped,Lattice.gauge,Forest.foldAt]
omit hp [Fintype I] in
lemma home_flat : orbitY F s s' k 0=0 := by rw [orbitY,home_base F s s' k H]; simp only [Pi.one_apply,plogC_one]; exact map_zero _
lemma snack : ContDiffAt ℝ ω (orbitY F s s' k) 0 := by
   unfold orbitY; refine (stand G F).symm.contDiff.contDiffAt.comp _ (contDiffAt_pi.mpr fun i=>?_); apply ContDiffAt.comp (g:=G.plog) (f:=fun z=>G.mat (preserveW F s s' k z i)) _ ?_ (plump F s s' k hp i); rw [home_base F s s' k H,Pi.one_apply,G.mat_one]; exact G.plog_diff
lemma swagger : ∀ᶠ z in 𝓝 0, exposure F 0 (stand G F (orbitY F s s' k z)) = preserveW F s s' k z := by
   have he i := (tendsto_pi_nhds.mp (show Tendsto (preserveW F s s' k) (𝓝 0) (𝓝 1) from home_base F s s' k H ▸ (plump F s s' k hp).cont.tendsto) i).eventually G.plog_right
   filter_upwards [eventually_all.mpr he] with z hz; funext i;simp only [orbitY,exposure, ContinuousLinearEquiv.apply_symm_apply,link_one, replica_one, Pi.one_apply,mul_one]; exact hz i
lemma swagger_fee : ∀ᶠ z in 𝓝 0, exposure F 0 (stand G F (orbitY F s s' k z)) = swivel F s s' k (z ∘ Sum.inr) (exposure F 0 (stand G F (z ∘ Sum.inl))) := by
   filter_upwards [swagger F s s' k hp H] with z hz; rw [hz,preserveW,rawcut,winged, sips]; rfl
lemma swagger_cut : ∀ᶠ z in 𝓝 0,input G f (offer G F (orbitY F s s' k z))=Lattice.gauge (scheme F s s' k z) (pull s (S.ratio.embed s') (input G f (winged F z))) := by
    filter_upwards [swagger F s s' k hp H] with z hz; rw [sips,hz,preserveW,Profiles.wears,Profiles.wiped];
    change Lattice.gauge _ (cook _ _ _ _ _)= _; unfold scheme; generalize F.foldAt _=k'; unfold cook; ext i; simp [Lattice.gauge,mul_assoc]
omit hp H [Fintype I] in
lemma scheme_parent (z : Rays (Pine G S F⊕I)) : scheme F s s' k z ∘ S.ratio.embed = k (z ∘ Sum.inr) := by
   funext i; simp [scheme,F.fold_root,ladenF,Ratio.embed_parent]
end YM.FormalBulk08.Reef
