import YM.Integration.WilsonThermometerWeakPrimary
import YM.TraceExtension.Prom.Port.Soft.Coupons

/-! The actual nonzero section through its full local angular grade. The covariance
is the mark-independent covariance of the booked physical weak detector. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPrimaryRead
open Function Set Filter Lattice Wilson RG Source Labels RG12 Extra.Histories
open PhysicalNext.Repeat.Legato Trace.Physical
open Next.Rank.Spindle Next.Rank Configuration Normal Rise Source.Drops
open Perch Glimmer LiftMark Beamer MvPolynomial Atlas Tariffs Station Ribbon
open WilsonThermometerWeakPrimary
open scoped ContDiff Topology BigOperators Classical
variable {G:Gauge} {C:Family G} {d k N p b m D e:ℕ}

theorem ray (C:Family G) (h:C.Makes) (grade:d≤D) :
    ∃ K:ℝ,∃ v:ℕ,0≤K ∧ ∀ {k N p b m e:ℕ} (rule:Rules G) (H:Provision C d k N p m b)
    (wide:4*b≤e) (_:C.ref d≤k) (_:k≤N) (x:C.label d)
    {rent cash:ℝ} (_:0≤rent) (q:poly (Up C k p b)),
    Summary rule (C.path.rep N p k).p b D (verseX C d k p) (verseA C d k p)
      (weights C (C.path.rep N p k).p.threshold x) rent cash q →
    coin (trim (unwind (o:=0) H.length wide d q) (key G d) d-expose (C.labels.level d) x)
        ≤ cash*rent*K*(1+(b:ℝ))^v*(C.path.rep N p k).p.threshold := by
  obtain ⟨s,a,c,v,ha,hc,rank,test⟩:=kiosk d D C.params
  refine ⟨c*a,v,mul_nonneg hc ha,?_⟩
  intro k N p b m e rule H wide hk hn x rent cash hr q summary
  obtain ⟨weights',hh,terms⟩:=summary
  let P:=(C.path.rep N p k).p
  let X:=expose (C.labels.level d) x
  let Y:=trim (unwind (o:=0) H.length wide d q) (key G d) d
  have trimX : trim X (key G d) d=X:=circle ..
  have trimY : trim Y (key G d) d=Y:=by ext i;unfold Y;simp only [trim_coeff];split_ifs <;>simp
  have trimmed : trim (Y-X) (key G d) d=Y-X:=by rw [trim_sub,trimX,trimY]
  have mass : coin q≤cash*rent:=terms.charge.trans (mul_le_mul_of_nonneg_right hh.2.2 hr)
  have cash0:=Planned.GuardedAtom.sumBudget_credit hh
  have threshold:=P.threshold_pos
  let bill:=cash*rent*c*(1+(b:ℝ))^v*P.threshold
  have bill0:0≤bill:=by dsimp [bill];positivity
  have cost (A:Snap G d) (ok:A∈s) : ‖aeval (kp d A) (Y-X)‖≤bill := by
    have origin := WilsonThermometerWeakPrimary.angular rule h hk hn H x q A terms grade
    have cell : aeval (kp d A) Y=evaluate_ray (walked (tacks (o:=(0:Site (C.side k p))) C.params H.length A) q) d :=by
      rw [show Y=trim _ _ _ from rfl,veneer _ H.length wide,ray_stamp]
    rw [map_sub,norm_sub_rev,cell,←show evaluate_ray _ d=aeval (kp d A) X from origin]
    apply (test A ok b _ _ H.length P q terms.produced.choose_spec.1.degree).2.trans
    dsimp [bill];gcongr
  exact (rank _ trimmed bill bill0 cost).trans_eq (by dsimp [bill];ring)

private theorem contraction {V Z:Type} (p:poly V) (w:Z→ℕ) (K:Normal.Symmetric V)
    (eps C:ℝ) (he:0≤eps) (he':eps≤1) (hc:1≤C)
    (cap:∀ i j,‖K.cov i j‖≤eps) (deg:p.totalDegree≤D)
    (f:V→Z→₀ ℂ) (cells:∀ i,cents (glyph (f i)) 0 1≤C) (signal:poly Z):
    coin (trim (exchange f (milk K p)) w d-signal) ≤
      coin (trim (exchange f p) w d-signal)+coin p*(eps*(2*(D+2))^D)*C^D := by
  obtain ⟨small,limit⟩:=bounds K D eps cap he he' p deg
  let U(q:poly V):=trim (exchange f q) w d
  let A:=U (milk K p)
  let B:=U p
  have eq : A-B=U (milk K p-p) :=by rw [show U (milk K p-p)=trim (exchange f (milk K p-p)) w d from rfl,map_sub,trim_sub]
  have h : coin (A-B) ≤ coin (milk K p-p)*C^D := by
    rw [eq]
    exact (trims 1 zero_le_one 0 w d _).trans (rise f 0 zero_le_one hc cells _
      ((totalDegree_sub ..).trans (max_le limit deg)))
  have sum : A-signal=(B-signal)+(A-B) :=by abel
  change coin (A-signal)≤_
  rw [sum]
  exact (taller 0 zero_le_one _ _).trans (add_le_add le_rfl
    (h.trans (mul_le_mul_of_nonneg_right small (pow_nonneg (zero_le_one.trans hc) _))))

variable (R:Run G)
local notation "A" => R.family.path.levels
local notation "T" => R.family.path.rep
local notation "F" => R.family.labels.level d
local notation "Corr" => WilsonThermometerWeakWickRoom.corrected R

theorem funded (simple:G.Simple) (S:Rules G) (d D:ℕ) (grade:d≤D):
    ∀ᶠ k:ℕ in atTop, ∀ N (_:k≤N) p,
    let n:=sizeQ R.family k
    let m:=scouts R.family k
    let P:=(T N p k).p
    ∃ (h:Provision R.family d k N p m n) (wide:4*n≤wood (A) k),∀ x:R.family.label d,
    D+1≤P.order → ∃ (rent:ℝ) (q:poly (Up R.family k p n)),
      0≤rent ∧ rent≤tin (clim (A) k) D ∧
      Summary S P n D (verseX R.family d k p) (verseA R.family d k p)
        (weights R.family P.threshold x) rent (2*(((A).params k).columns*(R.family.labels.level d).coeffSize x)) q ∧
      ∀ X:AtlasData G R.family.S p,Hail R.family k p D X →
        coin (Corr h.length wide (control (k:=k) X 0 (wood (A) k)) q N d-expose (R.family.labels.level d) x)
          ≤(2*(((A).params k).columns*(R.family.labels.level d).coeffSize x))*bill (-(1/2)) (clim (A) k) := by
  obtain ⟨K,v,K0,test⟩:=ray R.family R.makes grade
  obtain ⟨c,c0,posted⟩:=bind S D
  let a:=shade D
  have a0:0<a:=shade_pos D
  have rot : ∀ᶠ k:ℕ in atTop,(1+4*(sizeQ R.family k:ℝ))^D ≤bill a (clim (A) k) := by
    filter_upwards [setter R.family a a0 (4^D) simple R.makes D] with k hs
    apply le_trans _ hs;rw [←mul_pow];apply pow_le_pow_left₀ (by positivity);linarith only
  filter_upwards [eventually_ge_atTop (R.family.ref d),housing R.family d simple R.makes,
    checks R.family D c a simple a0,setter R.family a a0 K simple R.makes v,rot,
    WilsonThermometerWeakWickRoom.faceFee R.family d simple a0,booth (A) 1 simple,
    supports D R.family simple R.makes,WilsonThermometerWeakWickRoom.wallet R.family simple D] with
    k hk room lots geom turns cells floor mask arb N hn p n m P
  let s:=clim (A) k
  let M:=tin s D
  let e:=bill (-1) s
  have M1:1≤M:=tincost s D
  have M0:=zero_le_one.trans M1
  have e0:0≤e:=(Real.exp_pos _).le
  have e1:e≤1:= (billed s (show (-1:ℝ)≤0 by norm_num)).trans_eq (bill_zero _)
  let h:=room.2 p N hn
  let w:=room.1
  refine ⟨h,w,?_⟩
  intro x depth
  let C:=2*(((A).params k).columns*(R.family.labels.level d).coeffSize x)
  have nC:0≤C:=by dsimp [C];have:=((A).params k).columns_ge;positivity [Work.G08.size_nonneg (R.family.labels.level d) x]
  let rent:=((Fintype.card (Up R.family k p n):ℝ)+1)^D*c
  have nr:0≤rent:=by dsimp [rent];positivity
  have dr:rent≤M:=lots p
  have credit : Wrapper P (verseX R.family d k p) (verseA R.family d k p) (weights R.family P.threshold x) C :=by
    exact WilsonThermometerWeakPrimary.paid (C:=R.family) (p:=p) R.makes hk hn x
  obtain ⟨q,paid⟩:=posted _ _ _ n _ _ _ _ credit depth
  refine ⟨rent,q,nr,dr,paid,?_⟩
  intro X cov
  obtain ⟨h₀,body,words⟩:=paid
  have v0:=words.produced.choose_spec.1.degree
  have f : P.threshold≤e:=by rw [show P=(A).budget k from (R.makes.wilson.represents N p k hn).vac];exact floor
  have hK : K*(1+(n:ℝ))^v≤M:=geom
  have raw:=test S h w hk hn x nr q ⟨h₀,body,words⟩
  have cost : coin q≤C*M:=(words.charge.trans (mul_le_mul_of_nonneg_right body.2.2 nr)).trans
    (mul_le_mul_of_nonneg_left dr nC)
  let j:=rename (calls w) (dustAt h.length q)
  have j0 : coin j ≤ C*M^2 := (WilsonThermometerWeakWickRoom.curvature h.length w q v0).trans
    ((mul_le_mul cost turns (by positivity) (mul_nonneg nC M0)).trans_eq (by dsimp [M,tin,a];ring))
  let Q:=control (k:=k) X 0 (wood (A) k)
  let Z:=opq Q (↑((A).clock.threshold k/GaugeScale R.family k N p):ℂ)
  have fit:∀ i j,‖Z.cov i j‖≤e:=(mask N hn p).2.2 Q cov.2
  have degree : j.totalDegree≤D:=(totalDegree_rename_le ..).trans ((ascent _ _).trans v0)
  let fee:ℝ := (2*(D+2))^D
  have damp := contraction (d:=d) j (key G d) Z e M e0 e1 M1 fit degree (faceTest R.family d k) cells (expose (R.family.labels.level d) x)
  have fraw : coin (trim (unwind (o:=0) h.length w d q) (key G d) d-expose (R.family.labels.level d) x) ≤ C*(M^2*e) := by
    have rate:=mul_le_mul (mul_le_mul dr hK (by positivity) M0) f P.threshold_pos.le (mul_nonneg M0 M0)
    calc
      _ ≤ _ := raw
      _ = C*((rent*(K*(1+(n:ℝ))^v))*P.threshold) := by ring
      _ ≤ C*((M*M)*e) := mul_le_mul_of_nonneg_left rate nC
      _ = _ := by ring
  have rest : coin j*(e*fee)*M^D ≤ (C*M^2)*(e*fee)*M^D :=by gcongr
  have charge : M^2*e+M^2*e*fee*M^D ≤ bill (-(1/2)) s := by
    have z:0≤M^2*e:=by positivity
    have y:0≤M^2*e*fee*M^D:=by dsimp [fee];positivity
    apply le_trans _ arb
    change M^2*e+M^2*e*fee*M^D ≤ 2*M^2*e+2*M^2*e*fee*M^D
    linarith only [z,y]
  refine damp.trans ((add_le_add fraw rest).trans ?_)
  calc
    _ = C*(M^2*e+M^2*e*fee*M^D) :=by ring
    _ ≤ C*bill (-(1/2)) s:=mul_le_mul_of_nonneg_left charge nC

theorem original (simple:G.Simple) (S:Rules G) (d D:ℕ) (grade:d≤D):
    ∀ᶠ k:ℕ in atTop, ∀ N (_:k≤N) p,
    let n:=sizeQ R.family k
    let m:=scouts R.family k
    let P:=(T N p k).p
    ∃ (h:Provision R.family d k N p m n) (wide:4*n≤wood (A) k),∀ x:R.family.label d,
    D+1≤P.order → ∃ (rent:ℝ) (q:poly (Up R.family k p n)),
      Summary S P n D (verseX R.family d k p) (verseA R.family d k p)
        (weights R.family P.threshold x) rent (2*(((A).params k).columns*(R.family.labels.level d).coeffSize x)) q ∧
      ∀ X:AtlasData G R.family.S p,Hail R.family k p D X →
        coin (Corr h.length wide (control (k:=k) X 0 (wood (A) k)) q N d-expose (R.family.labels.level d) x)
          ≤(2*(((A).params k).columns*(R.family.labels.level d).coeffSize x))*bill (-(1/2)) (clim (A) k) := by
  filter_upwards [funded R simple S d D grade] with k stage N hn p n m P
  obtain ⟨h,w,rows⟩:=stage N hn p
  refine ⟨h,w,?_⟩
  intro x order
  obtain ⟨r,q,_,_,a,h⟩:=rows x order
  exact ⟨r,q,a,h⟩

end YM.Integration.WilsonThermometerWeakPrimaryRead
end
