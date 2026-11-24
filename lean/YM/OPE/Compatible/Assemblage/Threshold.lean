import YM.OPE.Compatible.Assemblage.Casting
import YM.OPE.Replicas.Aeolus
/-!
# Begin at actual finite sectors with markers headed for different clocks
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Stem
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {G:Gauge} {H:History G}{N p k j d:ℕ}{V I:Type} [Fintype V][DecidableEq V][Fintype I][DecidableEq I]{P:Ensemble V}
    {E:V→ Site (H.S.side N p)}
variable {u δ r:ℕ→ℝ}{s:ℕ→ℕ} {W: I→ℝ}
variable {D:∀ N p m:ℕ,m<N→GaugeDoor (H.rep N p (m+1)) (H.rep N p m)}
variable {X:I→ Stem V G (H.S.side N p)}{g:I→ V→ Config G (H.S.side N p)→ℂ}
structure Budges (P:Ensemble V)(H:History G) (N p:ℕ) (u W:ℝ)(E:V→ Site (H.S.side N p))(X: Stem V G (H.S.side N p))(b:V→ Config G (H.S.side N p)→ℂ) : Prop where
   pos:0 < W
   mark : Marked (H.rep N p N) E P X
   patent : ∃ (z : MergeProof.Response G (H.S.side N p))(r:ℝ), Attainment (H.rep N p N).p (X.home P.v) z r ∧ W*r ≤ u ∧ hook (H.rep N p N).activities (H.rep N p N).p.threshold z=profile (H.rep N p N).activities (X.gas P.v)
   writes U i : ((H.rep N p N).eval U:ℂ)*b i U=X.sub (H.rep N p N) i U
lemma flushed (hh:∀ j: I,Budges P H N p (u N) (W j) E (X j) (g j))(h:H.Selected)(hm: Moonlit H s δ u D)(hp:Occupancy (tags X) (s N)):
   Owns (H.rep N p N) E P X W ((H.levels.budget N).supportExponent-3) (birth (Names V I) (H.rep N p N) (fun j=>g j.2 j.1)):=by
   have hA:= h.represents N p N le_rfl; have hε:= hm.endow N; let Γ:= H.rep N p N; let p':=H.levels.budget N; have hP:= hA.vac; choose ψ t he hL hZ using fun j=>(hh j).patent
   let z(i:V×I):= if i.1=P.v then ψ i.2 else upwards (P.move i.1) (E i.1) (ψ i.2)
   have hy(i:V×I):Attainment Γ.p (tags X i) (z i) (t i.2):=by
      rcases i with ⟨i,j⟩; by_cases hi:i=P.v
      · subst i; simp only [z,if_true]; exact he j
      simp only [z,if_neg hi]; change Attainment _ ((X j).home i) _ _; rw [(hh j).mark.sym i hi]; exact rise _ _ (he j)
   obtain ⟨hc,hD,hψ,hI⟩:=hε; let e:= p'.supportExponent-3
   let π i:= (hA.good.labels.moves (P.move i).1 (E i)).some
   let w:=quota V W; have hw i: 0 < w i:= (hh i.2).pos
   have h₁: (((Γ.p.B+Γ.p.B+1:ℕ):ℝ))^4*(H.levels.clock.forcedAllowance N+s N*siteFactor Γ.p.B*u N) ≤ Γ.p.supportExponent-e:=by
      change ((( ((H.rep N p N).p.B+(H.rep N p N).p.B+1:ℕ):ℝ)))^4*(_+↑(s N)*siteFactor (H.rep N p N).p.B* u N) ≤ (H.rep N p N).p.supportExponent-((H.levels.budget N).supportExponent-3); rw [hP]; exact hψ.trans_eq (by ring)
   refine ⟨fun i=> (hh i).mark,fun i=> (hh i).pos,?_⟩
   have hv: Garnish Γ.p (tags X) z w Γ.p.supportExponent (u N):= cloth hy (fun i=>hL i.2) (fun i=>hw i|>.le)
   have hK i: Dominated (color X i):= (hh i.2).mark.spends _
   let T':= tags X; unfold ink
   apply spawn hA.good.labels z hv (by intro i hi;simp [z,hi]) (fun i _=> P.to_ref i) (fun i=>⟨π i⟩) hp hc hw le_rfl hD h₁ (by rw [hP]; exact hI) (fun U=>(Tour.bright H h N p _ le_rfl U).ne') zero_le_one hK ?_ ?_
   · rintro ⟨i,j⟩; by_cases hi:i=P.v
     · subst i; simp only [z,if_true]; exact hZ j
     unfold z; rw [if_neg hi]; rw [hooked (P.move i) (E i) (π i)]; change floatUp _ _ _=profile _ ((X j).gas i); rw [((hh j).mark.shine i hi).2]; exact congr_arg _ (hZ j)
   rintro ⟨i,j⟩; intro U; exact (hh j).writes U i
section
-- using main music at its printed scale
variable {M: Extraction.Order} {Z:Labels.Frame G d}{E₀:Hol G}(F:SectionData Z) {g:V→ Config G (H.S.side N p)→ℂ}
    {W:Bid.Worth}{X:Extra.Histories.Music Z H N p}{w z v: ℕ→ℝ}{t r₀:ℝ}{y: Z.Coeff}
    {Q:Stem V G (H.S.side N p)}
lemma authenticated (hS:Sung F H N p E₀ W k X)(hF:F.Sound E₀)(hp:Banks H Z t u z N)
    (hb : coverNumber (H.levels.budget N).B (F.footprint (0:Site (H.S.side N p))) ≤ 1)(hV : ∀ (i:Z.Index)(U:Config G (H.S.side N p)), ‖F.places (Size.axis Z i) 0 U‖ ≤ t)
    (hZ: profile (H.rep N p N).activities (((X.tone N).plays y).forced)=hook (H.rep N p N).activities (H.rep N p N).p.threshold (booster F (H.rep N p N) 0 y))
    (h:H.Selected)(hv:r₀*bond H N p X N y ≤ z N)(hr:0<r₀)(he:Stamp (N:=N) P F E ((X.tone N).plays y) Q)(hf:∀ i,g i=stepUp (P.move i) (Q.home i) (initial F H N p y 0)):
    Budges P H N p (u N) r₀ E Q g:=by
   have hh:= h.represents N p N le_rfl; let τ:= H.rep N p N; let a:= P.move P.v; let Y:=(X.tone N).plays y; let R:= booster F (H.rep N p N) 0 y; let i:= Q.home P.v
   obtain ⟨π⟩:= hh.good.labels.moves (1:Signed) i
   obtain ⟨x,hP,H'⟩:= erected H E₀ F W z u t k N p X y r₀ (hT:=hF) hV h hS hv hp hb hr.le
   have hw:= rise (1,false) i hP; rw [show affine (1:Signed) i 0=i by simp [affine]] at hw
   have hy:= stack_of hw (alto H N d); refine ⟨hr,he.homes,⟨(alto H N d) • upwards (1,false) i R,_,hy,H',?_⟩,?_⟩
   · rw [hook_scale]; unfold R; rw [hooked (1,false) i π,← hZ]; exact he.price.symm
   intro U j; obtain ⟨hh,hc⟩:= (hS.earned N hS.ahead le_rfl).earns y; rw [Stamp.equals_gauge F he h le_rfl hF hh hc j]; rw [hf j]; exact mural H E₀ F N p X y (P.move j) (Q.home j) hS.head h U
end
end YM.MergeProof.Ribbons.ManyCopies.Stem
