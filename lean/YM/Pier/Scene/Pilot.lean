import YM.Pier.Scene.Shore
/-! Real measuring frame and occupancy for projected native scene integral.
Entry prices via actual centers on R, all r. Pulling Dimes in the same Pegs' frame
where available; *no* comparison to the independent program. Geometry and
r/a margins explicitly kept. Some arithmetic adapted from Tarmac. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG17.Panoramic
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Marker Source Overlay
open FullVolume.Sever MergeProof MergeProof.Accent Extra.Histories Extra.Trajectories Extra.Multi Next.Rank Edition Spindle SharpGram Trace RG12 Next.UVStress
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
set_option quotPrecheck false
variable {G:Gauge}(R:Run G)(h:Flick R.family.path.levels){f:Extraction.Order} {S:Table R.family.book}{F:Spec.Final R.family f S} (L:Layout F)(W:OPE.Services R.family f S)
variable {m p N k n:ℕ}{Γ:Census (Fin n)}
local notation "C"=> R.family
local notation "A"=> R.family.path
local notation "Gx"=> Pert.Asymptotics.regulatorRun R.family
local notation "ρ"=> R.family.path.rep
local notation "ι"=> R.family.path.levels
local notation "H"=> R.family.path.levels.clock.hatBeta
local notation "a"=> R.family.S.a
local notation "Λ"=> fun i=> Real.log (H i)


include h W
private lemma monies {r:ℝ}(z x dα:ℕ) (k m:ℕ) (v:R.family.label z)(hm:m=L.level r)
    (hk:1≤ k) (he:R.family.ref z ≤ m)(ht:R.family.ref z≤k)(hx:k≤ N)(hy:m≤N) (hh: a m / a k ≤ (H k)^x) (hv: mass R.family z (L.shift z r v) ≤ (H k)^dα) :
    let y:= atRef L z r (N,p) v
    moneys R.family z k N p y ≤ (H k)^(1+x*(z+1)+dα):=by
   intro y; let b:=H k
   have hb :1 ≤b:= ((ι).fits.delayed k).le; have h₀: 0<b:= zero_lt_one.trans_le hb
   have hd: 1 ≤ b^x:= one_le_pow₀ hb
   have hf:=podQuota (i:=(N,p)) W hh hd F.room.cutoff y he ht hy hx
   have hpA : (0:ℝ)<a m:= (C).S.a_pos m
   have hpB : (0:ℝ)<a k:= (C).S.a_pos k
   have hp: quota C z m N p y= a m^z * mass C z ((L.shift z r) v):=by
      unfold y atRef; rw [← hm,quota_smul, quota_atK C F.room.cutoff _ _ (N,p) he hy,Complex.norm_real,Real.norm_of_nonneg (pow_pos hpA _).le]
      · exact R.makes
      · exact he
      exact hy
   let M:= mass C z (L.shift z r v)
   have hY:Spindle.paid C z k N p y= (a k^z)⁻¹ * quota C z k N p y:=by
      unfold Spindle.paid Price.awake; rw [Size.smul,norm_inv,norm_pow,Complex.norm_real,Real.norm_of_nonneg hpB.le]; rfl
   have ht: quota C z k N p y ≤ a k^z * (b^x)^(z+1) * b^dα:=by
      rw [hp] at hf
      exact hf.trans ((le_of_eq (show (a k/a m)^z*((b^x)^(z+1))*(a m^z*M) = a k^z*(b^x)^(z+1)*M from (by rw [div_pow]; field_simp))).trans (mul_le_mul_of_nonneg_left hv (by positivity))) -- hp pair inference m N p
   unfold moneys; apply le_trans (mul_le_mul (possibleOdds R h W hk) le_rfl (paid_pos ..) h₀.le); rw [hY]
   refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht (by positivity)) h₀.le).trans_eq ?_; change b * (_*_) = b^_; field_simp; ring
omit h -- use U
variable {h0:G.Simple}{T:Campaign R}{W':Campaign.Pillars R T}(U:Pier.Starter R h0 T W')
include U
lemma calmIntegral (d:Fin n→ℕ) (c e f' v' wide:ℕ)(hi:1≤wide) :
    ∀ᶠ k:ℕ in atTop,∀ l:ℕ,(R.family.path.levels.budget k).B^8 ≤ l→ (l:ℝ) ≤ (H k)^v' →
      ∀ N p:ℕ,k<N→∀ r:ℝ,L.level r≤N → (∀ j, R.family.ref (d j) ≤ L.level r) →
      a (L.level r)/a k ≤ (H k)^c →
      ∀ x:Fin n→ Site (R.family.side k p), (∀ k j, separation (x k) (x j) ≤ wide*l) →
       (∀ k j,k≠j→ l ≤ separation (x k) (x j)) →
      ∀ v:(j:Fin n)→ R.family.label (d j),
        (∀ j, mass R.family (d j) (L.shift _ r (v j)) ≤ (H k)^f')→
      ∀ s:Γ.Mode, Integrable (gapTag R N s x (shutter R L d r N p v)) (OPE.Therm.scene A N p k) ∧
        ‖∫ U,gapTag R N s x (shutter R L d r N p v) U∂(OPE.Therm.scene A N p k)‖ ≤
          2^e * Gx N p k^(2*e) := by
    obtain ⟨j,hj⟩:= (eventually_all.mpr (fun i:Fin n=>eventually_ge_atTop (1+c*(d i+1)+f'))).exists
    filter_upwards [allScenes (Γ:=Γ) R d U j e v' wide hi,eventually_ge_atTop 1,
      eventually_all.mpr (fun i:Fin n=>eventually_ge_atTop ((C).ref (d i)))] with k ht h1 h2 l hl hl' N p hk r hA hP he x hX hF v hv s
    apply ht l hl hl' N p hk x hX hF (fun i=>atRef L (d i) r (N,p) (v i)) _ s
    intro i'; have hp:= monies (r:=r) (p:=p) R U.flick L W _ _ _ k _ (v i') rfl h1 (hP i') (h2 i') hk.le hA he (hv i')
    exact (le_mul_of_one_le_left (paid_pos ..) (col_ge C k)).trans (hp.trans (pow_le_pow_right₀ ((ι).fits.delayed k).le (hj i')))

open OPE Spec
variable {y:Filter (ℕ×ℕ)}
    {u:Lenses.Mantle F y}(hL:Located L)(hZ : Comparably R L.level)(hM:Pegs u L)
local notation "k!" r => L.level (r)
local notation "w!" s r=> berth R ((s)+25) (L.level r)

omit W L U in
private lemma boots (P:Levels G) (h:G.Simple)(i j:ℕ)(he:i≤j):P.clock.hatBeta i ≤ P.clock.hatBeta j:= WilsonStartup.Timing.hat_mono P (Gauge.slopeConstant_pos h).le he
omit U W in
lemma snapshot_power (m k N p e:ℕ)(hm:m≤k)(he: k ≤ N)(hg:G.Simple) : (Gx N p k)^(2*e) ≤ 4^e * Gx N p m^(2*e) := by
    rw [pow_mul,pow_mul,← mul_pow]; apply pow_le_pow_left₀ (sq_nonneg _)
    have hh:(H k)⁻¹ ≤ (H m)⁻¹:= inv_anti₀ (zero_lt_one.trans ((ι).fits.delayed _)) (boots _ hg _ _ hm)
    exact ((payBand R he).2.1).trans ((mul_le_mul_of_nonneg_left (hh.trans (payBand R (p:=p) (hm.trans he)|>.2.2)) zero_le_two).trans_eq (by ring))
include hL hZ
/- both all-close and SNAP along any specified finite test. Keep **same Gx**; prove and pass price in both stop and reported units. -/
theorem wholeFrame (d:Fin n→ℕ)(o t e p':ℕ)(ht:1≤t) :
   ∀ᶠ r:ℝ in home, let m:= L.level r; let k:=berth R (o+25) m
   (m < k) ∧ Comparably R L.level ∧ EnvelopeRange R m k t o r ∧
    ((4*n:ℝ)* R.family.S.a k ≤ r/H m^o ∧ (4*n:ℝ)* R.family.S.a k ≤ r/(t:ℝ)/4) ∧
    ∀ X:Points n, AtShore t X→ ∀ p:ℕ,
     (∃ x:Fin n→Site (R.family.side k p), Neighbor R X r ((4*n:ℝ)*R.family.S.a k) x) ∧
     ∀ N:ℕ,k<N→∀ v:(j:Fin n)→ R.family.label (d j),
       (∀ j,mass R.family (d j) (L.shift _ r (v j)) ≤ (H m)^p')→
     ∀ x:Fin n→ Site (R.family.side k p), Neighbor R X r (r/(t:ℝ)/4) x →
     ∀ s:Γ.Mode, Integrable (gapTag R N s x (shutter R L d r N p v)) (Therm.scene A N p k) ∧
       ‖∫ Y,gapTag R N s x (shutter R L d r N p v) Y∂(Therm.scene A N p k)‖ ≤
          (8:ℝ)^e * Gx N p m^(2*e) := by
    let w r:= berth R (o+25) (L.level r)
    have hw:Tendsto w home atTop:=tendsto_atTop_mono (fun r=> (arrival R (o+25) (L.level r)).1.le) hL.level.growing
    have hc:1≤32*t^2:= by exact (Nat.mul_pos (by norm_num) (pow_pos ht (2:ℕ)))
    filter_upwards [positiveLength, planning R U L hL hZ o t ht, relative_round R U ht L hL hZ n o, eventually_all.mpr (fun j=>hL.level.growing.eventually_ge_atTop (R.family.ref (d j))), hw.eventually (calmIntegral R L W U d (o+27) e p' (o+29) (32*t^2) hc (Γ:=Γ))] with r hr hJ hE hc hb m k
    refine ⟨hJ.small,hZ,hJ,hE,fun X hX p=> ⟨ferry R ht hX hr hJ p, fun N ha v hv x hx s=>?_⟩⟩
    obtain ⟨h₁,h₂,h₃⟩:= fitsSnap R ht hX hr hJ x hx
    obtain ⟨hq,hV⟩:= hb (tick R r t k) hJ.extra h₃ N p ha r (hJ.small.trans ha|>.le) hc hJ.zoom x h₁ h₂ v (fun i=>(hv i).trans (pow_le_pow_left₀ (zero_lt_one.trans ((ι).fits.delayed m)).le (boots _ h0 _ _ hJ.small.le) _)) s
    exact ⟨hq,hV.trans ((mul_le_mul_of_nonneg_left (snapshot_power R _ _ _ _ _ hJ.small.le ha.le h0) (by positivity)).trans_eq (by rw [← mul_assoc, ← mul_pow]; norm_num; rfl))⟩

/- Pay measurements at fixed physical label *before* summing ANY derivative order with this
price; eventually every vector in Layout frame of free-space rank. Cost version with norm
v explicit for multilinear tools. -/
include hM
omit U hZ in
lemma shapesPay (p':ℕ) (d: ℕ) : ∀ᶠ r:ℝ in home, ∀ v: Free C d, ‖v‖≤ H (k! r)^p' → ∃ w : R.family.label d,
   mass R.family d (L.shift d r w) ≤ H (k! r)^(1+Lenses.price d+p') ∧ master L d r w= L.frame d r v ∧
   Filter.Tendsto (fun i=>atRef L d r i w) L.lens (𝓝 (locatedRef L d r w)) := by
    filter_upwards [engineeringPass u L W hM d, (Station.hat_rate (ι) W.simpleGate|>.comp hL.level.growing).eventually_ge_atTop 2, hL.level.growing.eventually_ge_atTop (R.family.ref d)] with r hs hQ ht v hv
    obtain ⟨w,hw,hQ'⟩:= hs.1 v
    let t:= (L.shift d r).symm w; letI := L.notbot
    refine ⟨t,?_,?_,tendsRef L (v:=fun _=>t) le_rfl tendsto_const_nhds ht⟩ -- args
    · let q:= H (k! r); rw [show L.shift d r t=w from LinearEquiv.apply_symm_apply ..]; have hf:0<q:=zero_lt_one.trans ((ι).fits.delayed _); exact hw.trans ((mul_le_mul (mul_le_mul_of_nonneg_right (show 2≤ q from hQ) (pow_nonneg hf.le _)) hv (norm_nonneg _) (by positivity)).trans_eq (by unfold q; ring))
    change engineering (L.charts) d _ (L.shift d r t) = _; rw [show L.shift d r t=w from LinearEquiv.apply_symm_apply ..]; exact hQ'

end YM.RG17.Panoramic
