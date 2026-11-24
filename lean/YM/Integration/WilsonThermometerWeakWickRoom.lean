import YM.Integration.WilsonThermometerWeakWick

/-! Price of the actual compensated stable polynomial on the weak clock.
The scaled covariance retains precisely the self-contractions entering the
same physical date's normal-ordered calibration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakWickRoom
open Function Filter Set Lattice Wilson RG Source Labels RG12 Extra.Histories
open PhysicalNext.Repeat.Legato Trace.Physical GermGraph
open Next.Rank.Spindle Next.Rank Configuration Normal Rise Source.Drops
open Perch Glimmer LiftMark Beamer MvPolynomial Atlas Tariffs Station
open WilsonThermometerWeakTaylor
open scoped Classical Topology BigOperators
variable {G:Gauge} {d D:ℕ} {F:Frame G d}

theorem curvature {n:Side} {b R:ℕ} (live:2*(b+1)<n.val) (he:4*b≤R)
    (q:poly (links G (0:Site n) b)) (cap:q.totalDegree≤D) :
    coin (rename (calls he) (dustAt live q)) ≤ coin q*(1+4*(b:ℝ))^D := by
  let J:=dustAt live q
  have h1 : coin (rename (calls he) J) ≤coin J := by
    rw [Normal.labelled]
    have h:=rise (fun z:slotC G b=> Finsupp.single (calls he z) (1:ℂ)) 0 zero_le_one
      (c:=1) le_rfl (fun z=>by simp) J le_rfl
    simpa only [one_pow,mul_one] using h
  refine h1.trans (rise _ 0 zero_le_one (by simp) ?_ _ cap)
  intro i
  have paid := prices (word G live i.1) i.2
  have len : (↑(word G live i.1 |>.length):ℝ) ≤4*b :=by exact_mod_cast lengths_word G live i.1
  exact paid.trans (len.trans (le_add_of_nonneg_left zero_le_one))

theorem faceFee (C:Family G) (d:ℕ) (hg:G.Simple) {a:ℝ} (ha:0<a) :
    ∀ᶠ k:ℕ in atTop,∀ i,cents (glyph (faceTest C d k i)) 0 1≤bill a (clim C.path.levels k) := by
  obtain ⟨c,_,bound⟩ := Glimmer.display (G:=G) (d:=d)
  filter_upwards [(hat_rate C.path.levels hg).eventually (roomier d ha c)] with k ht x
  let T:=wood C.path.levels k
  unfold faceTest LiftMark.ink glyph
  rw [map_sum]
  apply (Rise.collect _ zero_le_one ..).trans
  apply le_trans _ ((bound T x.val ((tracing ..).1 x.property)).trans ht)
  apply Finset.sum_le_sum
  intro i _
  rw [Finsupp.linearCombination_single]
  apply (retiring _ _).trans
  rw [Complex.norm_real]
  simp only [coin,Rise.pay_X,one_pow,mul_one];exact le_rfl

theorem wallet (C:Family G) (hg:G.Simple) (D:ℕ) :
    ∀ᶠ k:ℕ in atTop,
    let s:=clim C.path.levels k
    let H:=tin s D
    let e:=bill (-1) s
    let K:ℝ:=(2*(D+2))^D
    2*H^2*e + 2*H^2*e*K*H^D ≤ bill (-(1/2)) s := by
  let α:=shade D
  let E:=2*(1+(2*((D:ℝ)+2))^D)
  have gap : α*((D:ℝ)+2)+(-1)< -(1/2:ℝ) := by linarith only [shade_thin D]
  filter_upwards [(hat_rate C.path.levels hg).eventually (transports gap E)] with k cost
  let s:=clim C.path.levels k
  let H:=tin s D
  let e:=bill (-1) s
  let K:ℝ:=(2*(D+2))^D
  have pl:1≤H:=tincost s D
  have el:0≤e:=(Real.exp_pos _).le
  have align : H^2*e*H^D=bill (α*((D:ℝ)+2)+(-1)) s := by
    unfold H e tin bill α
    rw [←Real.exp_nat_mul,←Real.exp_nat_mul,←Real.exp_add,←Real.exp_add];congr 1;ring
  change 2*H^2*e + 2*H^2*e*K*H^D ≤ _
  calc
    _ ≤ 2*H^2*e*H^D+2*H^2*e*K*H^D :=
      add_le_add (le_mul_of_one_le_right (by positivity) (one_le_pow₀ pl)) le_rfl
    _ = E*(H^2*e*H^D) := by unfold E K;ring
    _ ≤ _ := align ▸ cost

variable (R:Run G)
local notation "A" => R.family.path.levels
local notation "S₀" => R.family.path.rep
def corrected {k p b:ℕ} (live:2*(b+1)<(R.family.side k p).val)
    (he:4*b≤wood (A) k) (cov:Normal.Symmetric (trimV (wood (A) k) G))
    (q:poly (links G (0:Site (R.family.side k p)) b)) (N d:ℕ) :=
    let t:=(A).clock.threshold k
    let g:=GaugeScale R.family k N p
    trim (exchange (faceTest R.family d k) (milk (opq cov (↑(t/g):ℂ))
      (rename (calls he) (dustAt live q)))) (key G d) d

theorem funded (hg:G.Simple) (S:Rules G) (d D:ℕ) (degree:d≤D) :
    ∀ᶠ k:ℕ in atTop, ∀ N (_:k≤N) p,
    let n:=sizeQ R.family k
    let m:=scouts R.family k
    let T:=(S₀) N p k
    ∃ (live:2*(n+1)<(R.family.side k p).val) (wide:4*n≤wood (A) k),
    ∀ (X:Coefficient (R.family.labels.level d) (R.family.side k p))
      (_:X.Format 0 R.family.params T) {κ cash:ℝ} (_:X.remBound 0 T κ cash),
    D+1≤T.p.order →
    ∃ (rent:ℝ) (u w:poly (links G (0:Site (R.family.side k p)) n)),
      0≤rent ∧ rent≤tin (clim (A) k) D ∧
      Summary S T.p n D (fun j:Near (P:=T) X m=>X.support j) (fun j=>X.regular j) (fun _=>1) rent cash u ∧
      Summary S T.p n D (fun j:Far (P:=T) X m=>X.support j) (fun j=>X.regular j) (fun _=>1) rent (expCut T.p m*cash) w ∧
      ∀ Q:Normal.Symmetric (trimV (wood (A) k) G),(∀ i j,‖Q.cov i j‖≤tin (clim (A) k) D) →
        coin (corrected R live wide Q (u+w) N d) ≤ cash*bill (-(1/2)) (clim (A) k) := by
  obtain ⟨c,c0,posted⟩:=WilsonThermometerWeakTaylor.original (F:=R.family.labels.level d) (H:=R.family.params) S D
  obtain ⟨K,v,K0,angular⟩:= WilsonThermometerWeakWick.angular (F:=R.family.labels.level d) R.family.params degree
  let a:=shade D
  have a0:0<a:=shade_pos D
  have lift : ∀ᶠ k:ℕ in atTop,(1+4*(sizeQ R.family k:ℝ))^D ≤ bill a (clim (A) k) := by
    filter_upwards [setter R.family a a0 (4^D) hg R.makes D] with k hs
    apply le_trans _ hs;rw [← mul_pow];apply pow_le_pow_left₀ (by positivity);linarith only
  filter_upwards [housing R.family d hg R.makes,checks R.family D c a hg a0,
    setter R.family a a0 K hg R.makes v,lift,faceFee R.family d hg a0,booth (A) 1 hg,
    shrank R.family 1 hg R.makes,supports D R.family hg R.makes,wallet R.family hg D] with
    k house rentCost stage lifted cells floor small law close N hk p n m T
  let s:=clim (A) k
  let H:=tin s D
  let e:=bill (-1) s
  have H1:1≤H:=tincost s D
  have H0:=zero_le_one.trans H1
  have e0:0≤e:=(Real.exp_pos _).le
  have e1:e≤1:= (billed s (show (-1:ℝ)≤0 by norm_num)).trans_eq (bill_zero _)
  let placed:=house.2 p N hk
  let wide:=house.1
  let live:=placed.length
  refine ⟨live,wide,?_⟩
  intro X form κ cash paid order
  let rent:=((Fintype.card (Up R.family k p n):ℝ)+1)^D*c
  have r0:0≤rent:=by dsimp [rent];positivity
  have r1:rent≤H:=rentCost p
  have small' : expCut T.p m≤e:=small N hk p
  have floor' : T.p.threshold≤e:=by rw [show T.p=(A).budget k from (R.makes.wilson.represents N p k hk).vac];exact floor
  obtain ⟨u,w,nu,fw⟩ := posted X m n form paid order
  refine ⟨rent,u,w,r0,r1,nu,fw,?_⟩
  intro Q base
  obtain ⟨α,hα,hu⟩:=nu
  obtain ⟨β,hβ,hw⟩:=fw
  have c0:=Planned.GuardedAtom.sumBudget_credit hα
  have g0 : 0≤expCut T.p m:=(Real.exp_pos _).le
  have hc : coin (u+w)≤2*cash*H := by
    have z:= (Rise.taller 0 zero_le_one u w).trans (add_le_add (hu.charge.trans (mul_le_mul_of_nonneg_right hα.2.2 r0))
      (hw.charge.trans (mul_le_mul_of_nonneg_right hβ.2.2 r0)))
    calc
      _ ≤ _ := z
      _ ≤ cash*H + (1*cash)*H := add_le_add (mul_le_mul_of_nonneg_left r1 c0)
        (mul_le_mul (mul_le_mul_of_nonneg_right (small'.trans e1) c0) r1 r0 (by positivity))
      _ = _ := by ring
  let J:=rename (calls wide) (dustAt live (u+w))
  have deg : (u+w).totalDegree≤D :=
    (totalDegree_add ..).trans (max_le hu.produced.choose_spec.1.degree hw.produced.choose_spec.1.degree)
  have mass : coin J≤2*cash*H^2 := (curvature (G:=G) live wide (u+w) deg).trans
    ((mul_le_mul hc lifted (by positivity) (by positivity)).trans_eq (by dsimp [H,tin,a];ring))
  have old := angular X S placed.cap live placed.cuts wide form r0 u w ⟨α,hα,hu⟩ ⟨β,hβ,hw⟩
  have step : coin (trim (unwind (o:=0) live wide d (u+w)) (key G d) d)≤cash*(2*H^2*e) := by
    have geom : K*(1+(n:ℝ))^v≤H:= stage
    have rate := mul_le_mul (mul_le_mul r1 geom (by positivity) H0)
      (add_le_add floor' small') (add_nonneg T.p.threshold_pos.le g0) (mul_nonneg H0 H0)
    calc
      _ ≤ _ := old
      _ = cash*((rent*(K*(1+(n:ℝ))^v))*(T.p.threshold+expCut T.p m)) := by ring
      _ ≤ cash*((H*H)*(e+e)) := mul_le_mul_of_nonneg_left rate c0
      _ = _ := by ring
  let Z:=opq Q (↑((A).clock.threshold k/GaugeScale R.family k N p):ℂ)
  have fit:∀ i j,‖Z.cov i j‖≤e:=(law N hk p).2.2 Q base
  let fees:ℝ:=(2*(D+2))^D
  have more := WilsonThermometerWeakWick.corrected (d:=d) live wide Z e H e0 e1 H1 fit (u+w) deg cells
  have co : coin J*(e*fees)*H^D ≤ (2*cash*H^2)*(e*fees)*H^D := by
    gcongr
  refine more.trans ((add_le_add step co).trans ?_)
  calc
    _ = cash*(2*H^2*e+2*H^2*e*fees*H^D) := by ring
    _ ≤ cash*bill (-(1/2)) s := mul_le_mul_of_nonneg_left close c0

theorem original (hg:G.Simple) (S:Rules G) (d D:ℕ) (degree:d≤D) :
    ∀ᶠ k:ℕ in atTop, ∀ N (_:k≤N) p,
    let n:=sizeQ R.family k
    let m:=scouts R.family k
    let T:=(S₀) N p k
    ∃ (live:2*(n+1)<(R.family.side k p).val) (wide:4*n≤wood (A) k),
    ∀ (X:Coefficient (R.family.labels.level d) (R.family.side k p))
      (_:X.Format 0 R.family.params T) {κ cash:ℝ} (_:X.remBound 0 T κ cash),
    D+1≤T.p.order →
    ∃ (rent:ℝ) (u w:poly (links G (0:Site (R.family.side k p)) n)),
      Summary S T.p n D (fun j:Near (P:=T) X m=>X.support j) (fun j=>X.regular j) (fun _=>1) rent cash u ∧
      Summary S T.p n D (fun j:Far (P:=T) X m=>X.support j) (fun j=>X.regular j) (fun _=>1) rent (expCut T.p m*cash) w ∧
      ∀ Q:Normal.Symmetric (trimV (wood (A) k) G),(∀ i j,‖Q.cov i j‖≤tin (clim (A) k) D) →
        coin (corrected R live wide Q (u+w) N d) ≤ cash*bill (-(1/2)) (clim (A) k) := by
  filter_upwards [funded R hg S d D degree] with k stage N hn p n m T
  obtain ⟨live,wide,rows⟩:=stage N hn p
  refine ⟨live,wide,?_⟩
  intro X format κ cash paid order
  obtain ⟨r,u,w,_,_,a,b,h⟩:=rows X format paid order
  exact ⟨r,u,w,a,b,h⟩

end YM.Integration.WilsonThermometerWeakWickRoom
end
