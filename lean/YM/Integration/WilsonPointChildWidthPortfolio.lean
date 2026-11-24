import YM.Integration.WilsonPointChildNormalizedWidth

/-! A single width bill for every retained channel and angular grade of
    the restored original fixed-residue source. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPointChildWidthPortfolio
open YM FormalBulk08 Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Dove Dove.Lab Sierra
open PhysicalNext.Repeat.Legato Next.Foundations Borough
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open WilsonPointChildNormalizedWidth WilsonNeutralPointCourse WilsonPointChildFiledPress WilsonPointChildFiledSalary
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge} {d D:ℕ} {o:Loc G 1}

theorem restrict {F:Frame G d}{Y:Plaza F D}{E l:ℕ}{b C:ℝ}(w:Wallet o F Y b E C)(he:l≤E):
    Wallet o F Y b l C:=⟨w.nonneg,fun s p j hj r hr=>w.tested s p j (hj.trans he) r (hr.trans (by omega))⟩

theorem mono {F:Frame G d}{Y:Plaza F D}{E:ℕ}{b C M:ℝ}(w:Wallet o F Y b E C)(h:C≤M):
    Wallet o F Y b E M:=⟨w.nonneg.trans h,fun s p j hj r hr=>
      (w.tested s p j hj r hr).mono (mul_le_mul_of_nonneg_right h (norm_nonneg _))⟩

def invoice (F:Frame G d)(M:Tilework F)(E:ℕ):ℝ:=1+∑ x:Letter F×Fin (E+1),inverseCost F M x.1 x.2.val

theorem invoice_pos (F:Frame G d)(M:Tilework F)(E:ℕ):1≤ invoice F M E:=by
  unfold invoice inverseCost
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>abs_nonneg _)

theorem invoice_pays (F:Frame G d)(M:Tilework F){E e:ℕ}(he:e≤E)(s:Letter F):
    inverseCost F M s e ≤ invoice F M E:=by
  let x:Letter F×Fin (E+1):=⟨s,⟨e,by omega⟩⟩
  have non (z:Letter F×Fin (E+1)):0≤ inverseCost F M z.1 z.2.val:=
    Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>abs_nonneg _
  exact (Finset.single_le_sum (fun z _=>non z) (Finset.mem_univ x)).trans (le_add_of_nonneg_left zero_le_one)

theorem original (R:Run G)(wood:Primer.Families R.family)(a:hue G)(depth:d<D)
    (o:Loc G 1)(simple:G.Simple){orders:ℕ→ℕ}(granted:WilsonWindowFormalPurchase.Canonical orders R.kit)
    (E:ℕ):∀ᶠk:ℕ in atTop,∀(A B:Tour R k→ℕ→ℝ),
    (∀z j,k≤j→j≤z.cutoff→0≤A z j)→(∀z j,k≤j→j≤z.cutoff→1≤B z j)→
    (∀z j,k≤j→j<z.cutoff→Wallet o (R.family.labels.level d) (filed R wood a depth z.digit z.cutoff (j+1)) 0 E (A z (j+1)))→
    (∀z j,k≤j→j<z.cutoff→Wallet o (R.family.labels.level d) (filed R wood a depth z.digit z.cutoff (j+1)) (width R (j+1)) E (B z (j+1)))→
    ∃c:ℝ,∃w:ℕ,0≤c ∧ ∀z:Tour R k,∀j,k≤j→j<z.cutoff→
      Wallet o (R.family.labels.level d) (filed R wood a depth z.digit z.cutoff j) (width R j) E
        (invoice _ (transfer R wood a depth z.digit z.cutoff j)⁻¹ E *
         (c*(max 1 (ageZ (R.family.path.levels.clock.hatBeta j)))^w)*
           ((1+A z (j+1))*(B z (j+1))^(WilsonPinnedWidthTransport.fraction R.family.S (width R) j))) :=by
  let X:=Fin (E+1) × Fin (d+E+1)
  have entry:=fun x:X=>WilsonPointChildNormalizedWidth.original R wood a depth o simple granted x.1.val x.2.val
  filter_upwards [Filter.eventually_all.mpr entry] with k funded
  intro A B ha hb low top
  choose c v cn pay using fun x:X=>funded x A B ha hb
    (fun z j kj head=>restrict (low z j kj head) (by omega))
    (fun z j kj head=>restrict (top z j kj head) (by omega))
  let M:=∑x,c x
  let w:=∑x,v x
  have cm (x:X):c x≤M:=Finset.single_le_sum (fun i _=>cn i) (Finset.mem_univ x)
  have vw (x:X):v x≤w:=Finset.single_le_sum (fun i _=>Nat.zero_le (v i)) (Finset.mem_univ x)
  have Mn:0≤M:=Finset.sum_nonneg (fun i _=>cn i)
  refine ⟨M,w,Mn,?_⟩
  intro z j kj live
  let q:=1+A z (j+1)
  let h:=(B z (j+1))^(WilsonPinnedWidthTransport.fraction R.family.S (width R) j)
  let day:=max 1 (ageZ (R.family.path.levels.clock.hatBeta j))
  have dn:1≤day:=le_max_left ..
  have cn':0≤q:=add_nonneg zero_le_one (ha z _ (by omega) live)
  have hn:0≤h:=Real.rpow_nonneg (zero_le_one.trans (hb z _ (by omega) live)) _
  have pred:0≤ invoice _ (transfer R wood a depth z.digit z.cutoff j)⁻¹ E:=zero_le_one.trans (invoice_pos ..)
  refine ⟨mul_nonneg (mul_nonneg pred (mul_nonneg Mn (pow_nonneg (zero_le_one.trans dn) _))) (mul_nonneg cn' hn),?_⟩
  intro s p l ll r rr
  let x:X:=(⟨l,by omega⟩,⟨r,by omega⟩)
  have b:=pay x z j kj live s p
  apply b.mono
  have hpow:=mul_le_mul (cm x) (pow_le_pow_right₀ dn (vw x)) (pow_nonneg (zero_le_one.trans dn) _) Mn
  have fees:=mul_le_mul (invoice_pays _ (transfer R wood a depth z.digit z.cutoff j)⁻¹ ll s) hpow
    (mul_nonneg (cn x) (pow_nonneg (zero_le_one.trans dn) _)) pred
  have hit:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right fees (mul_nonneg cn' hn)) (norm_nonneg p)
  simpa only [x,q,h,day,mul_assoc] using hit

end YM.Integration.WilsonPointChildWidthPortfolio
