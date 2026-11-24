import YM.Integration.WilsonThermometerWeakPrimaryRead

/-! The chart jet of the complete actual addressed singleton at its first weak
report. Keep its canonical section and both signed stable polynomials on the
same group configuration before applying the physical Gaussian correction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakColumnRead
open Function Filter Set Lattice Wilson RG Source Labels RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Trace.Physical Push.Local GermGraph Next.Rank.Spindle Next.Rank Configuration Normal Rise Source.Drops
open Perch Glimmer LiftMark Beamer Atlas Tariffs MvPolynomial Ribbon
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonThermometerOwnOffsetNectar WilsonThermometerOwnOffsetTale
open WilsonThermometerWeakTaylor WilsonThermometerWeakPrimaryRead
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G)
local notation "A" => R.family.path.levels
local notation "B" => WilsonThermometerOffsetLedger.cash R
local notation "Corr" => WilsonThermometerWeakWickRoom.corrected R

theorem add {k N p b d:ℕ} (live:2*(b+1)<(R.family.side k p).val) (wide:4*b≤wood (A) k)
    (Q:Normal.Symmetric (trimV (wood (A) k) G)) (f g:poly (Up R.family k p b)) :
    Corr live wide Q (f+g) N d=Corr live wide Q f N d+Corr live wide Q g N d := by
  unfold WilsonThermometerWeakWickRoom.corrected
  simp only [dustAt,_root_.map_add,trim_add]

/-- The original aperture, canonical section, compensated coordinate, and
regular and hard parts are all witnessed on precisely the submitted field. -/
theorem funded (simple:G.Simple) (d D:ℕ) (hd:d≤D) (S:Rules G) (α:ℝ) :
    ∀ᶠ k:ℕ in atTop,∀ N (hn:k≤N) p,
    let P:=R.family.path.rep N p k
    let n:=sizeQ R.family k
    let m:=scouts R.family k
    let F:=R.family.labels.level d
    ∃ (h:Provision R.family d k N p m n) (wide:4*n≤wood (A) k),D+1≤P.p.order →
    ∀ (z:Site (R.family.side N p)) (V:Sight R.family d p) (r:Emblems R.family d)
      (_:Enrolled R.makes R.doors B k N p d (digits R N p z) V r) (y:Palette R.family d),
    let cash:=B d k*size y
    ∃ X:Coefficient F (R.family.side k p),∃ (a b:ℝ) (q u v:poly (Up R.family k p n)),
      0≤a ∧ a≤tin (clim (A) k) D ∧ 0≤b ∧ b≤tin (clim (A) k) D ∧
      X.Format 0 R.family.params P ∧ X.remBound 0 P (kappa R.family.path k) cash ∧
      View.Signpost P (1,false) (site R hn z) (invoice X 0 (R.family.localSection d) P)
        (state (k:=k) R V r y z k) ∧
      Germ.projection F R.family.params P.p.threshold 0 X=y (primaryLetter d) ∧
      F.coeffSize (@Sub.sub F.Coeff _ (y (primaryLetter d)) X.x) ≤ GermGraph.price (C:=R.family) d*
        Real.exp (α*R.family.S.scale k)*cash ∧
      Summary S P.p n D (verseX R.family d k p) (verseA R.family d k p)
        (WilsonThermometerWeakPrimary.weights R.family P.p.threshold X.x)
        a (2*(((A).params k).columns*F.coeffSize X.x)) q ∧
      Summary S P.p n D (fun i:Near (P:=P) X m=>X.support i) (fun i=>X.regular i)
        (fun _=>1) b cash u ∧
      Summary S P.p n D (fun i:Far (P:=P) X m=>X.support i) (fun i=>X.regular i)
        (fun _=>1) b (expCut P.p m*cash) v ∧
      ∀ E:AtlasData G R.family.S p,Hail R.family k p D E →
        coin (Corr h.length wide (control (k:=k) E 0 (wood (A) k)) (q+(u+v)) N d-expose F X.x)
          ≤ (2*(((A).params k).columns*F.coeffSize X.x)+cash)*bill (-(1/2)) (clim (A) k) := by
  filter_upwards [WilsonThermometerWeakPrimaryRead.funded R simple S d D hd,
      WilsonThermometerWeakWickRoom.funded R simple S d D hd,
      WilsonThermometerWeakTaylor.head (d:=d) R simple α] with k main reg gem N hn p P n m F
  obtain ⟨h,wide,prim⟩:=main N hn p
  obtain ⟨_,_,remainder⟩:=reg N hn p
  refine ⟨h,wide,?_⟩
  intro degree z V r H y cash
  obtain ⟨X,germ,format,paid,revealed⟩:=WilsonThermometerOwnOffsetWeakRows.singleton R z hn y H
  obtain ⟨a,q,na,ca,report,coarse⟩:=prim X.x degree
  obtain ⟨b,u,v,nb,cb,fresh,old,noise⟩:=remainder X format paid degree
  have head:=gem N p hn X (y (primaryLetter d)) ⟨format,paid⟩ germ
  refine ⟨X,a,b,q,u,v,na,ca,nb,cb,format,paid,revealed,germ,head,report,fresh,old,?_⟩
  intro E funded
  let Q:=control (k:=k) E 0 (wood (A) k)
  let Z:=Corr h.length wide Q q N d
  let H:=Corr h.length wide Q (u+v) N d
  let x:=expose F X.x
  have eq : Corr h.length wide Q (q+(u+v)) N d-x=(Z-x)+H := by rw [add];dsimp [Z,H];abel
  change coin (Corr h.length wide Q (q+(u+v)) N d-x)≤_
  rw [eq]
  refine (taller 0 zero_le_one _ _).trans ((add_le_add (coarse E funded) (noise Q funded.2)).trans_eq ?_)
  ring

theorem original (simple:G.Simple) (d D:ℕ) (hd:d≤D) (S:Rules G) (α:ℝ) :
    ∀ᶠ k:ℕ in atTop,∀ N (hn:k≤N) p,
    let P:=R.family.path.rep N p k
    let n:=sizeQ R.family k
    let m:=scouts R.family k
    let F:=R.family.labels.level d
    ∃ (h:Provision R.family d k N p m n) (wide:4*n≤wood (A) k),D+1≤P.p.order →
    ∀ (z:Site (R.family.side N p)) (V:Sight R.family d p) (r:Emblems R.family d)
      (_:Enrolled R.makes R.doors B k N p d (digits R N p z) V r) (y:Palette R.family d),
    let cash:=B d k*size y
    ∃ X:Coefficient F (R.family.side k p),∃ (a b:ℝ) (q u v:poly (Up R.family k p n)),
      X.Format 0 R.family.params P ∧ X.remBound 0 P (kappa R.family.path k) cash ∧
      View.Signpost P (1,false) (site R hn z) (invoice X 0 (R.family.localSection d) P)
        (state (k:=k) R V r y z k) ∧
      Germ.projection F R.family.params P.p.threshold 0 X=y (primaryLetter d) ∧
      F.coeffSize (@Sub.sub F.Coeff _ (y (primaryLetter d)) X.x) ≤ GermGraph.price (C:=R.family) d*
        Real.exp (α*R.family.S.scale k)*cash ∧
      Summary S P.p n D (verseX R.family d k p) (verseA R.family d k p)
        (WilsonThermometerWeakPrimary.weights R.family P.p.threshold X.x)
        a (2*(((A).params k).columns*F.coeffSize X.x)) q ∧
      Summary S P.p n D (fun i:Near (P:=P) X m=>X.support i) (fun i=>X.regular i)
        (fun _=>1) b cash u ∧
      Summary S P.p n D (fun i:Far (P:=P) X m=>X.support i) (fun i=>X.regular i)
        (fun _=>1) b (expCut P.p m*cash) v ∧
      ∀ E:AtlasData G R.family.S p,Hail R.family k p D E →
        coin (Corr h.length wide (control (k:=k) E 0 (wood (A) k)) (q+(u+v)) N d-expose F X.x)
          ≤ (2*(((A).params k).columns*F.coeffSize X.x)+cash)*bill (-(1/2)) (clim (A) k) := by
  filter_upwards [funded R simple d D hd S α] with k stage N hn p P n m F
  obtain ⟨h,w,rows⟩:=stage N hn p
  refine ⟨h,w,?_⟩
  intro order z V r H y cash
  obtain ⟨X,a,b,q,u,v,_,_,_,_,row⟩:=rows order z V r H y
  exact ⟨X,a,b,q,u,v,row⟩

end YM.Integration.WilsonThermometerWeakColumnRead
end
