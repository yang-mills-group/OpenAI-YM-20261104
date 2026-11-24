import YM.FormalBulk08.Primer.Limits
import YM.FormalBulk08.Annex.View

noncomputable section
set_option autoImplicit false
/-! ### Integration interface: Fields
Single primary contour in the Fk formal tower. It runs on independent
power inputs and *before* any on-shell/Gram, on same Section stencils.
The resetting P here is the *prescribed* off-shell projection, not the factory from Final.
The latter calibrates actual readout; proving their quantitative matching is for
consumers. Alphabet is Frame index × all derivative test stubs in total
weight d. Profile pull through block is there even in marked unit. Can use
C^D on ancestor harbor, or centered reference version exactly (cf.
`Annex.*`). `Avenue.*`, `Tundra.*` and `Taft.*` include further supplies for
leading* prescription, D stable, matched analytic cylinders and constant
bridge from fully-inverted leading lift WITH graph payments, respectively. -/
namespace YM.FormalBulk08.Primer
open Lattice Laurent Bloch RG Precision Wilson Filter Function Set
open scoped Topology BigOperators ENNReal Matrix ContDiff Classical Matrix.Norms.Frobenius
open Next.Free Reef Flat Orb Wick Series Mesa Jets City Cork Bank Wine Dove Dove.Lab
open Gorge Lava Lotus Shore North Quire Elm Borough Spigot Delphi Kemp Dawn Pose Rial Drift Rift Palm
open Stationary hiding seat Rays
open Aster PhysicalNext.Repeat.Legato Next.Foundations Roof
open PowerSeries Planned.PrimaryIntegral295 Place
variable {G:Gauge}(C:Family G)(h:G.Simple)(a:hue G)(L: Families C)(o:Loc G 1)
variable {U:ℕ→ℕ}{k i E e J d D r:ℕ}
variable (p:Announced C U)(hJ:5 ≤ J)(hk:J ≤ C.path.levels.clock.J (k+1))(hE:E≤J)(hd:d<D)(hX:d+3≤J)(hY:D≤J)

def fieldCoeffs (N i:ℕ) := Elm.terrace (chart G) C.path.levels L (Hay.Wday _) a (C.labels.level d) (C.localSection d) (show d+1≤D from hd) N i
def fieldLimit (i:ℕ):= Drift.issue (ChamberU C L 0) (chart G) a (C.labels.level d) (C.localSection d) (show d+1≤D from hd) PUnit.unit i
def fieldStep (N i:ℕ):= Elm.bornM (ρ:=chart G) (T:=C.localSection d) (W:=ChamberU C L 0) a (show d+1≤D from hd) PUnit.unit N i

include p in
/-- Angular polynomial test basis data on SAME stencil. In particular no

extra complex `LinearIndependent` premise or dimension assumption. -/
lemma fieldStarts (N q:ℕ)(z:Letter (C.labels.level d)):
    let F := C.labels.level d; let T:=fieldCoeffs C a L hd N N; let n:= C.S.side N q; let w:=mint F z; let i:= slots F z
    T=Rial.sectionY (C.localSection d) (show d+1≤D from hd) ∧
    X^i*Kemp.banner i (T z (inside F z D)) n= Jets.paste (fun x:Rays (wire G n)=> ((C.localSection d).places (copy F w) 0 (input G n x)).re) := by
   intro F T n w i; have he:T= Rial.sectionY (C.localSection d) (show d+1≤D from hd):= terrace_zero ..; refine ⟨he,?_⟩
   rw [he, sticker (C.localSection d) hd z z rfl]; exact debut _ _ _ le_rfl n (p.inputs d)
include h p hJ hk hX hY
lemma primal (x:k ≤ i)(N:ℕ)(hi:i ≤ N) :
    let T:= fieldCoeffs C a L hd N; let F:= C.labels.level d
    Court o F (T i) ∧ (∀ s:Signed,Harmonized F s (T i)) ∧ (i<N →
       let S:=fieldStep C a L hd N i; let v:= migrates a (destination C.path.levels N i) (L i) (Noise C) (densityCoeff C L a N (i+1)) (chart G) (Hay.Wday _ _) (Elm.growL _ i) d d
       Colfax (Pose.slots F) (Pose.weight F) S (fun u=> Grail.heightK (C.S.block i) d (Pose.weight F u)) ∧
        T i=larch (v ∘ T (i+1)) S⁻¹ ∧ larch (T i) S=v ∘ T (i+1)):= by
    intro T F; have H:= scripted C h L p hJ hk; have Z:= H.spare d D o J J hX hd hY le_rfl le_rfl; have ht:=p.available.sections d; let X:= indexN C L x
    refine ⟨birth a (chart_ok _) Z h ht (p.inputs d) X.a i N x hi,harmony a (chart_ok _) Z h ht (p.inputs d) X.a i N x hi,?_⟩; intro hz S v
    obtain ⟨V,W⟩:= mat_begins a (chart_ok _) Z h ht (p.inputs d) X.a i N x hz
    exact ⟨V,Elm.thickets _ _ _ _ _ _ _ _ _ _ hz,W⟩
lemma liftedByKernel (x:k ≤ i)(N:ℕ)(hi:i<N)(e r:ℕ) (w:Letter (C.labels.level d))(t:∀ n:Side,(primary (altitudeN C N i).patch (Noise C) n).Choices):
    let S:= fieldCoeffs C a L hd N; let P:= altitudeN C N i; let W:=densityCoeff C L a N (i+1)
    ∃ η:ℝ,0 < η ∧ ∀ p:Studio D,
       let z:= S (i+1) w; Kalm η (0,o) (quick P (L i) W z (chart G) (Hay.Wday _ _) (growL _ i) d d p e r)
            (fun n:Side=>rancho (quickP P (L i) W z (chart G) (Hay.Wday _ _) (growL _ i) d d p n (t n)) e r):= by
    intro S P W; have H:= primal C h a L o p hJ hk hd hX hY (x.trans (Nat.le_succ _)) N hi
    obtain ⟨η,v,H,-⟩:= brig o P (L i) _ W (chart G) (Hay.Wday _ i) (H.1.officers w).fare (genu C.path.levels L (Hay.Wday _) (chart G) a (chart_ok _) h (i:=i+1) (N:=N) hi).toStory (chart_ok _) (growL _ i) (C.path.levels.clock.adm i) (slotsFits _ _) t e r d
    exact ⟨η,v,H⟩
include o hE
/-- For use in comparison: any finite degree/horizon budget. `compress`
an exact centered (cube) formulation. Y difference vs FINER UV-end for the
COMPATIBLE graph (theorems in `Castor` for horizon change). -/
lemma landedFields (w:Letter (C.labels.level d)) (r):
    ∃ c m,0≤(c:ℝ) ∧ ∀ i:ℕ,k ≤ i → ∀ p':Studio D,∀ e:ℕ,e ≤ E →
      let z:= ageZ (C.path.levels.clock.hatBeta i); let b:= (FamilyWindow C).width (C.path.levels.clock.J i)
      let Y:=fieldLimit C a L hd i w p' e r; let S:= fun n=>fieldCoeffs C a L hd n i w p' e r
      let P:=‖Annex.compress D p'‖; let K:=c*z^(m:ℕ)
      Boone S Y ∧ Knoxville (fame _) b (0,o) Y (K*P) ∧ ∀ N:ℕ,i≤ N→ Knoxville (fame _) b (0,o) (S N) (K*P) ∧ Knoxville (fame _) b (0,o) (S N-Y) (K*ratioR C.S N i targetPower * P):= by
    have H:= scripted C h L p hJ hk; have Z:= H.spare d D o J E hX hd hY le_rfl hE; have ht:=p.available.sections d
    have hz:d≤J:= by omega
    obtain ⟨B,⟨c,m,hc,P⟩,Y⟩:= Annex.settles Z (H.vac _ hE) (chart_ok _) a h ht (p.inputs d) hz w
    refine ⟨c,m,hc,fun i hi P' e he=>?_⟩; intro V b T S j K; let x:= indexN C L hi
    have hc:B x ≤ K:= by unfold K; rw [← show _=V from (show (chron _|>.day x) = V from Borough.measure p.power i)]; exact (le_abs_self _).trans (P x)
    refine ⟨Drift.harbor Z (H.vac _ hE) (chart_ok _) a h ht (p.inputs d) hz he w r x P',(Y x P' e he r).1.mono (mul_le_mul_of_nonneg_right hc (norm_nonneg _)),fun N h=>?_⟩; obtain ⟨A,Q⟩:=(Y x P' e he r).2 N h; exact ⟨A.mono (mul_le_mul_of_nonneg_right hc (norm_nonneg _)),Q.mono (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (ratioR_pos ..).le) (norm_nonneg _))⟩

-- Π_o. Need projection through E (not claiming normalization at higher orders
-- than what is paid). Inputs still Probe in shared frame. No limit for truncated
-- expectation at the final long-range reader asserted.
lemma adjacent_limit (x:k ≤ i)(y w:Letter (C.labels.level d))(p':Studio D) (he:e≤ E)(r):
    let F:=C.labels.level d; let Y:=fieldLimit C a L hd; let X:= indexN C L x;let V:= mover (chart G) a X d d; let S:= Roof.pantry F (V ∘ Y (i+1))
    V (Y (i+1) y) p' e r=larch (Y i) S y p' e r ∧ Through E (pantry F (Y i) w y) ((1:Tilework F) w y) := by
   intro F T X V S; have H:= scripted C h L p hJ hk; have Z:= H.spare d D o J E hX hd hY le_rfl hE; have ht:=p.available.sections d; exact ⟨clapper Z (H.vac _ hE) (chart_ok _) a h ht (p.inputs d) (by omega) X y p' he r,stipulated Z (H.vac _ hE) (chart_ok _) a h ht (p.inputs d) (by omega) X w y⟩
end YM.FormalBulk08.Primer
