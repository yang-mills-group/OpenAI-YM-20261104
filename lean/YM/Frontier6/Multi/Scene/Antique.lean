import YM.MergeProof.North.Antique
import YM.Frontier6.Multi.Scene.Thumb

/- Generalization of YM/MergeProof/North/Antique. Propagation with
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
set_option quotPrecheck false
variable {σ ι δ p q k:ℝ}{N':ℕ}
variable {k':Live V feathers→ℕ→ Config G c→ℂ}{L':Live V feathers→ Config G c→ℂ}
    {ζ Z ξ ν ρ:ℝ}
-- stronger raw authorities. attach+Y so users exact bake. with bounds.Full.
lemma ranch (hD:Tunes D)(hs: SoundDoor S D)(hx:chimes v P E B o (S.ratio.parent ∘ o) L K (fun i=>profile A.activities (k' i)) g S)(π:∀ i,R.activities.Moves (P i).1 (S.ratio.embed (E i)))(hw:∀ i,0<w i)(hy:∀ i,i≠v→∀ j:feathers,w (i,j)=w (v,j)) (hp:∀ i:feathers, let y:Live V feathers:=(v,i);∃ x:Set Wing,x.Finite∧Tale x (o y) (S.ratio.parent (o y)) 1 (L y) (K y) (profile A.activities (k' y)) (g y) (a i) (t i) D) (hP:Occupancy o N)(hd:0 ≤ d)(he:u+1 ≤ R.p.supportExponent)(ha:∀ i:Live V feathers,2*w i*a i.snd ≤ d)(hK:∀ i:Live V feathers,w i*t i.snd ≤ x)(hY:e+1 ≤ A.p.supportExponent+2)
    (hg:R.Lawful σ δ q p k)(hh: Serves R L K Y v P (fun i=> S.ratio.embed (E i)) B o w u c') (hb:0≤ u) (hi:Arsenal R)(hS:S.IsKernel R.beta G) (hH:Occupancy (S.ratio.parent ∘ o) N')(hM:Unites S D N' u Z ζ e ν ξ) (hQ:let T:=N*siteFactor R.p.B*d+4*c'; T+Real.exp T*T ≤ Z) :
    Arc A L' k' (S.push R.beta Y) v P E B (S.ratio.parent ∘ o) w ζ e ν ξ x g:=by
    obtain ⟨I,hI,M,hX,hU,ψ,hψ,h'ψ,hT,hX'⟩:= propels hD hs hx π hw hy hp hP hd he ha hK hY hg hh hb hi
    obtain ⟨F,O,hR,h₁,hO,h₂,hA,hV,hE,hTT⟩:= hM feathers _ _ V _ _ I hI o w M hw hH (hU.fatten hQ)
    have hp0: Horn v P E B F O:=by
       intro i hv; obtain ⟨q,hq⟩:= hX i hv; exact ⟨hq.here,hTT _ _ _ _ _ _ _ hq (fun j=>(hy i hv j).symm)⟩
    refine ⟨F,O,ψ,hψ,h'ψ,hR,hO,h₁,h₂,hp0,hV,fun i j U=> ?_,funext fun U=>?_⟩
    · rw [hE]; exact (congr_fun (hT j i) U).symm
    let s:=Mach X g; let b:=fun U=>∑ i,F i U; let f' U:= s+b U
    rw [show Y=(fun U=>_) from funext hX',convective S _ _ hS (heat M S w hg),hA];
    unfold play; rw [pass_add (mute X g) (show (b U).part (X).quiet=0 from ?_), mul_smul_comm];
    · unfold b; rw [mul_assoc]
    unfold b; rw [Poly.part_sum]; exact Finset.sum_eq_zero (fun j _=> (h₁ j).sil U)
end YM.MergeProof.Canopies
