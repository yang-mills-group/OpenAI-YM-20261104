import YM.Frontier6.Multi.Scene.Wraith
import YM.MergeProof.North.Thumb
import YM.Frontier6.Multi.Scene.Platform

/- Generalization of YM/MergeProof/North/Thumb. Propagation with
   a genuinely shared per-copy program over *all* finitely many active
   insertions, and same coherences on all internal modes. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Canopies
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories
open scoped Topology BigOperators Classical
variable {V : Type}[Fintype V] {feathers : Type}[DecidableEq feathers][Fintype feathers][DecidableEq V]{G:Gauge}{f c:Side}{R:Rep G f}{A:Rep G c}{D:GaugeDoor R A}{S:StepData c f}
variable {v:V}{P:V→Motion}{E:V→Site c}{B:V→Equiv.Perm V}
local notation "X"=> Now V feathers
variable {o:Live V feathers→ Site f}{b:Live V feathers→Site c}
    {L:Live V feathers→ Config G f→ℂ}{K:Live V feathers→ Res G f}{H:Live V feathers→ Res G c}{a t:feathers→ℝ}{g:Live V feathers→ℂ}
    {N:ℕ} {d e u x φ ψ c':ℝ}{w:Live V feathers→ℝ}
    {Y: Config G f→Poly (Now V feathers)}
local notation "r"=> fun i=> S.ratio.embed (E i)
-- H,K raw ways. final exact operation. preserve on Mom. needed for any lower steps, split raw branch after exponent.
lemma Harps {m:Motion}{B:Equiv.Perm V}{p q:Poly (Now V feathers)}(h:Harm v B m p q): Harm v B m (octave p) (octave q):=by
   intro s hs; by_cases he: 2 ≤ s.val.card
   · rw [crest _ _ he,crest _ _ (show 2 ≤ (drum B s).val.card from (by rw [drum,pares, card_image_of_injective _ (nome B).injective];exact he))]; exact h s hs
   rw [starlet _ _ (Nat.lt_of_not_ge he),starlet _ _ (show (drum B s).val.card<2 from (by rw [drum,pares, card_image_of_injective _ (nome B).injective]; exact Nat.lt_of_not_ge he)),scalar_z]
-- After Blanket pliable maybe broad generalized.
structure Arc (R:Rep G f)(L:Live V feathers→ Config G f→ℂ)(K:Live V feathers→ℕ→ Config G f→ℂ)(Y:Config G f→ Poly (Now V feathers))(v:V)(P:V→Motion)(E:V→Site f)(B:V→Equiv.Perm V)(o:Live V feathers→Site f)(w:Live V feathers→ℝ)(d e t a b:ℝ)(pepper:Live V feathers→ℂ): Prop where
    see : ∃ F Z, ∃ (ψ:Live V feathers→ Response G f), Garnish R.p o ψ w e b∧ relates v P E ψ ∧ Towed w id F R.p.B d t ∧ Towed w Prod.fst Z R.p.B e a ∧ (∀ i,Burns o i (F i) R.p.threshold) ∧(∀ i,Flow o i (Z i) R.p.threshold)∧ Horn v P E B F Z ∧ (∀ i U,(Z i U).part (Now V feathers).quiet=profile R.activities (fun j=>Complex.ofReal ∘ R.activities.K j) i U)∧(∀ i j U,(Z i U).part ((Now V feathers).fire j)+hook R.activities R.p.threshold (ψ j) i U=profile R.activities (K j) i U)∧ Y= play R (Now V feathers) Z (fun U=> Mach (Now V feathers) pepper+∑ i,F i U)
variable {k:Live V feathers→ℕ→ Config G c→ℂ}{L':Live V feathers→ Config G c→ℂ}
    {Z':Config G c→Poly (Now V feathers)}{ζ Z ξ ν ρ:ℝ}
lemma thru (p:Arc A L' k Z' v P E B b w (u+ζ) e x φ c' g)(hA:A.activities.Valid A.p d ν)(hw:∀ i,0<w i)(hu:0 ≤ c')(hp:Occupancy b N)(ht:0 ≤ u+ζ)(hk:((A.p.B+A.p.B+1:ℕ):ℝ)^4*(φ+N*siteFactor A.p.B*c')≤e-(u+ζ))
    {w':Live V feathers→ℝ}(hw':∀ i,0<w' i)(hB:Repegs b A.p.B w w' ζ Z (Now V feathers))(hz:0≤ Z)(he:Z*x ≤ ξ)(hh:Z*(Real.exp (φ+ N*siteFactor A.p.B*c')-1)≤ ξ)(hC:∀ i U,(Z' U).part ((Now V feathers).fire i)=coin A (L' i) (k i) U)(hy:∀ i,Dominated (k i))(hit:∀ U,A.eval U≠0): Serves A L' (fun i=>profile A.activities (k i)) Z' v P E B b w' u ξ:=by
    obtain ⟨F,K,ψ,ha,hr,hT,hW,hF,hH,ho,hI,hP,rfl⟩:=p.see
    let l U:= Mach (Now V feathers) g+∑ i,F i U; have hn:∀ U: Config G c,(l U).part (Now V feathers).quiet=0:=by intro U; unfold l; simp_rw [Poly.part_plus,Poly.part_sum,mute, show ∀ i,(F i U).part (Now V feathers).quiet=0 from (fun i=> (hF i).sil U),sum_const_zero,add_zero]
    obtain ⟨H,hQ,hN,hJ⟩:= curtainC A ψ K l ha hH hI hA hn (fun U s hp=> by unfold l; rw [Poly.part_plus,hush _ _ hp,zero_add]) hw hu hp hF hT hW (by ring) ht hk hw' hB hz he hh hP hC hy hit
    refine ⟨_,_,H,hQ,hN, ?_,hJ⟩
    intro i hi; have ho:= ho i hi; exact ⟨ho.1,fun U=> ⟨fun s=> Harps ((ho.2 U).1 s),fun j=> Harps (reborn v i _ _ _ K ψ _ _ ho.1 (hr _ hi) ((ho.2 U).2) j)⟩⟩
end YM.MergeProof.Canopies
