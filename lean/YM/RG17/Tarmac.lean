import YM.RG17.Lull
import YM.RG17.Beads
import YM.RG17.Feather
import YM.RG17.Refresh
/-!
# Full-power result in NO-FLAG slice for marks in THIS measured layout

 Keep rough bills explicitly -- after every set of demands choose slate with
 sufficient geometry (here legs spaced by B²). Needs calibration on
 legs, we do prove power price for settings with indicated mass. No Taylor approximation in step variable! NEXT match/mass/OPE margin uses all domains.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
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
lemma possibleOdds (hk:1≤ k) : ((ι).params k).columns ≤ H k:=by
  obtain ⟨J,r,T,Q⟩:= W.purchase
  obtain ⟨i,rfl⟩:= Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
  exact (OPE.Columns.column_small Q.system.costs.back).trans ((h.grade i).trans ((by linarith only [Real.log_le_sub_one_of_pos (zero_lt_one.trans ((ι).fits.delayed i))] : Real.log (H i)≤ H i).trans (WilsonStartup.Timing.hat_mono _ (Gauge.slopeConstant_pos W.simpleGate).le (Nat.le_succ i)))) -- namespace

-- ${g}$-power allowance choosing AFTER k from real contours. k = stop at capture, m= L.level r ; if k>m must be paying still.
def draught (R:Run G)(k D n:ℕ) :ℝ:= (R.family.path.levels.clock.hatBeta k^ n)⁻¹*(fly R.family.path.levels D k)

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

variable (d:Fin n→ℕ) (c i:ℕ)
-- capacity in Poly Census AFTER calibration. Profile grams only Tech. uniformly in s maybe via finitely many states externally
local notation "wB"=> fun k s:ℕ=> draught R k s (1+c*(s+1)+i)
private lemma paidToll (s:Γ.Mode)(k): Poly.toll (fun j=> wB k (d j)) s = (H k)⁻¹^(∑ j∈ s.val, (1+c*(d j+1)+i+winter G (d j))):=by
   unfold Poly.toll; rw [← Finset.prod_pow_eq_pow_sum]
   apply Finset.prod_congr rfl; intro j _; unfold draught fly fog; rw [pow_add,inv_pow,inv_pow]

omit h in
lemma briskFee : ∀ z,∀ᶠ k:ℕ in atTop, (H k)^ (z:ℕ) ≤ brisk ((R.family.path.levels.budget k).B) :=by
    have hh:Tendsto (fun i=> Real.log (H i)) atTop atTop:= Real.tendsto_log_atTop.comp (Station.hat_rate _ W.simpleGate)
    intro z; filter_upwards [hh.eventually_ge_atTop (64*z)] with k hk
    let a':ℝ:= H k; let l:= Real.log a'
    change a'^z ≤ _
    unfold brisk
    have hz:64* z ≤ l:= hk
    apply (Real.log_le_iff_le_exp (pow_pos (zero_lt_one.trans ((ι).fits.delayed k)) _)).mp
    rw [Real.log_pow, le_div_iff₀ (by norm_num)]
    have hx:0 ≤ l:=le_trans (by positivity) hz
    exact (show (z:ℝ)*l*64 ≤ l^2 from by nlinarith only [mul_le_mul_of_nonneg_left hz hx]).trans (Nat.le_ceil _)

private lemma spendOrder (r:ℕ)(s:Γ.Mode): ∃ Q:ℝ,0 ≤ Q ∧ ∀ᶠ k:ℕ in atTop, ∀ N p:ℕ,k≤N→
    Real.exp (n*(3+1:ℝ)) / Poly.toll (fun j=> wB k (d j)) s / (brisk ((R.family.path.levels.budget k).B)/2) ≤ Q * Gx N p k ^(2*r) :=by
   let B:= Real.exp (n*(3+1:ℝ)); let z:= ∑ j∈ s.val, (1+c*(d j+1)+i+winter G (d j))
   refine ⟨(2*B*2^r),by unfold B; positivity,?_⟩
   filter_upwards [briskFee R W (z+r)] with k hk N p he
   rw [paidToll R h W] -- implicit inputs h W
   let b:= H k; let A':= Gx N p k
   have hb:0<b:= zero_lt_one.trans ((ι).fits.delayed k)
   let D:= brisk ((ι).budget k).B
   have hz: b^(z+r) ≤ D:= hk
   have he':b⁻¹ ≤ 2*A'^2 := (payBand R he).2.2
   change B/b⁻¹^z/(D/2) ≤ 2*B*2^r * A'^(2*r)
   calc _ ≤ B/b⁻¹^z/(b^(z+r)/2):= div_le_div_of_nonneg_left (by unfold B; positivity) (by positivity) (by linarith only [hz])
        _ = 2*B*b⁻¹^r:= by rw [pow_add, inv_pow,inv_pow]; field_simp
        _ ≤ _:= (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_pos.mpr hb).le he' r) (show 0≤2*B from by unfold B;positivity)).trans_eq (by ring)

-- actual conditional departure from product of singletons. uniform p *all*, atRef same all-r. Existence exact type r : ℝ used for layout. k,m relation payment specified. No seam smoothing inferred.
abbrev shutter (r:ℝ)(N p:ℕ)(v:(j:Fin n)→R.family.label (d j)) : Fin n→R.family.book.Token := fun j=> ⟨d j, atRef L _ r (N,p) (v j)⟩
-- erect embedded markers at real reporting stop. adapted stencil example. use general Migrating too.
abbrev attachV (k:ℕ) (x:Fin n→Site (R.family.side k p))(j:ℕ)(l:Fin n):= Ribbons.loops R.family k p (x l) j
lemma erect {k N:ℕ}(x:Fin n → Site (R.family.side k p)) : Migrating R.family.path k p N (attachV R k x):= by
   constructor; intro i h he; funext j
   unfold attachV Function.comp; dsimp only; rw [Ribbons.vect R.family k p i (x j) h,Ribbons.vect R.family k p (i+1) _ (h.trans (Nat.le_succ _))]; exact (Station.embed_comp (R.family.S.toDepth h p) ((A).levels.clock.op i p).ratio _ _).symm
include L
lemma allClear (T:ℕ):∃ Q:ℝ, 0 ≤ Q ∧ ∀ᶠ k:ℕ in atTop, ∀ N p:ℕ, k<N→∀ r:ℝ, L.level r ≤ N → (∀ j,R.family.ref (d j)≤ L.level r) → a (L.level r)/a k ≤ H k^c →
    ∀ v: (j:Fin n)→ R.family.label (d j), (∀ j, mass R.family (d j) (L.shift _ r (v j)) ≤ H k^i)→
      ∀ x:Fin n→ Site (R.family.side k p),
        (∀ i l,i≠l → (R.family.path.levels.budget k).B^2 ≤ separation (x i) (x l))→
          let o:= attachV R k x
          let y:= shutter R L d r N p v
          -- estimate applied to every part. further alignment conditions for using at THAT protocol.
          ∀ U,flags (A|>.rep N p k).p.threshold U=∅ → ∀ s:Γ.Mode,
          ‖pullDimes y (p:=p) (N:=N) (o N) s k U / (boardMass C N p k U:ℂ) - ∏ j∈s.val,lines17 y (p:=p) o N k j U‖ ≤ Q * Gx N p k ^ (2*T):=by
    let D(k):= brisk ((ι).budget k).B
    choose Q hp hT using spendOrder R h W d c i T (Γ:=Γ)
    obtain ⟨M,hM,hB⟩:= ((eventually_ge_atTop (0:ℝ)).and (eventually_all.mpr fun j=>eventually_ge_atTop (Q j))).exists
    refine ⟨M,hM,?_⟩
    have he : ∀ᶠ i:ℕ in atTop,2<D i:=by
         filter_upwards [briskFee R W 1,(Station.hat_rate _ W.simpleGate).eventually_gt_atTop 2] with k hk hv
         rw [pow_one] at hk; exact lt_of_lt_of_le hv hk
    filter_upwards [he,eventually_all.mpr hT,eventually_ge_atTop 1,eventually_all.mpr (fun j=>eventually_ge_atTop (C|>.ref (d j)))] with k hz hT hk hP N p ha r hr hj hx v hv x he o y U hh s
    let P':= (A).rep N p k; let b:= (ι).budget k
    let w j:= wB k (d j)
    have hl : P'.p=b:=(R.makes.wilson.represents N p k ha.le).vac
    obtain ⟨W',r',D',F'⟩:= W.purchase
    have hL: 0 ≤ b.supportExponent-3:= (F'.system.costs.pond (N:=k) (k:=k) (p:=p)).night.endow.2.1
    have hw(j):0 < w j:= mul_pos (inv_pos.mpr (pow_pos (zero_lt_one.trans ((ι).fits.delayed k)) _)) (inv_pos.mpr (pow_pos (zero_lt_one.trans ((ι).fits.delayed k)) _))
    have hS : ∀ j l, j≠l → b.B^2 ≤ separation (o k j) (o k l):=by
        intro j l h; rw [show o k j=x j from Ribbons.same (C) k p _, show o k l=x l from Ribbons.same (C) k p _]; exact he j l h
    have hq (j:Fin n) : w j * moneys R.family (y j).fst k N p (y j).snd ≤ fly R.family.path.levels (y j).1 k:= by
      have hp: moneys R.family (d j) k N p (y j).2 ≤ H k ^ (1+c*(d j+1)+i):= monies R h L W (d j) -- fix args
         _ _ _ _ (v j) rfl hk (hj j) (hP j) ha.le hr hx (hv j)
      refine (mul_le_mul_of_nonneg_left hp (hw j).le).trans (le_of_eq ?_); unfold w draught; field_simp [(pow_pos (zero_lt_one.trans ((ι).fits.delayed k)) _).ne']; rfl
    obtain ⟨hs,hA,g,hX⟩:= openedStorm  W F.room.cutoff y (p:=p) o (Γ:=Γ) ha (erect R h W x) hS hP hw hq
    rw [← hX] at hs hA
    have h':2 < brisk P'.p.B:= hl.symm ▸ hz
    have hhU:=gentleScene g hs hA hw (by linarith only [hL]) (show Drake Γ P'.p.B (o k) from by rw [hl]; exact ⟨fun _ _ j _ t _ h=> hS j t h⟩) (hl.symm ▸ F'.system.costs.stay.support k (Nat.zero_le _)) h' U hh s
    rw [show (R.family.path.rep N p k).p.B = ((ι).budget k).B from congr_arg BudgetPoint.B hl] at hhU; exact hhU.trans ((hT s N p ha.le).trans (mul_le_mul_of_nonneg_right (hB _) (pow_nonneg (payBand R ha.le).1.le _)))
end YM.RG17
