import YM.Integration.WilsonPositionProgramTrialPublicJointFourActiveCourse

/-! A common payroll for all genuine forward active blocks and their report-clock changes. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true

namespace YM.Integration.WilsonPositionProgramTrialPublicJointFourActiveBudget

open WilsonCoeffUV WilsonCoeffUV.RootLaw
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Supply Ticket Polestar Shard Plan Mer
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
open Matrix PowerSeries Finset
open scoped BigOperators Classical
variable {G:Gauge}{F:Frame G 4}

open WilsonPositionProgramTrialPublicJointFourActiveKernel (watch watched)
open WilsonPositionProgramTrialPublicJointFourActiveCredit (Pass run)
open WilsonIndependentMatchedFreshInverseIncome (age)
variable {D e:ℕ}{T:SectionData F}{fit:4<D}{H:Hol G}{V W Z:Credit}

open WilsonPositionProgramTrialPublicJointFourActiveCourse (forward)

theorem kinetics (H:Hol G)(T:SectionData F)(p:4<D)(e:ℕ)(E W K:Credit): ∃ V:Credit,∀ (t:CourseS H T p e E W K)(i j:ℕ),i ≤ e → j ≤ e → let A:=t.vols; let B n:= relativeF A.draws A.paid n t.spur t.length; twain (V.buy t.Age) t.cab (coeff i ((B t.I.n)^j)) (coeff i ((B t.I.N)^j)):=by
    let S:= (Finset.range (e+1))×ˢ(Finset.range (e+1)); let P (k:ℕ×ℕ)(C:Credit): Prop:=∀ t:CourseS H T p e E W K, let A:=t.vols; let B n:= relativeF A.draws A.paid n t.spur t.length; twain (C.buy t.Age) t.cab (coeff k.1 ((B t.I.n)^k.2)) (coeff k.1 ((B t.I.N)^k.2))
    have H : ∀ i∈ S,∃ V:Credit,P i V:=by
       rintro ⟨i,j⟩ h; have hx:i < e+1:=Finset.mem_range.mp (Finset.mem_product.mp h).1
       let F (t:WindowS G (e+1) E) (n):= relativeF t.robe.draws t.robe.paid n t.base t.span
       obtain ⟨d,C,h,H⟩:= clipped_pow (WindowS.payments G (e+1) E) (i:=i) (p:=fun t:WindowS G (e+1) E=>F t t.n) (q:=fun t:WindowS G (e+1) E=> F t t.N) j (fun i g=> ascend G (e+1) i E (by omega))
       let V: Credit:= ⟨d,max 1 C,le_max_left ..⟩; refine ⟨V,?_⟩; intro t G J
       have hp :C*t.Age^d ≤ V.buy t.Age:= mul_le_mul_of_nonneg_right (le_max_right ..) (pow_nonneg (zero_le_one.trans t.I.warm) _)
       have ht:= (H t.I).lift hp (trail_pos ..).le; dsimp only [F,Pi.pow_apply] at ht; rw [t.peace] at ht; exact ht
    obtain ⟨X,f⟩:= uniformPays (P:=P) S (fun i hi=> H i hi) (fun i _ x y v H=> by intro t A B; exact (H t).lift (v _ t.I.warm) (trail_pos ..).le); exact ⟨X,fun t i j v h=>f (i,j) (Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩) t⟩

theorem seats (H:Hol G)(T:SectionData F)(fit:4<D)(e:ℕ)(V W Z:Credit)(simple:G.Simple):
    ∃C:Credit,∀(c:CourseS H T fit e V W Z)(q:ℕ),q ≤ e → ∀i j:Alma F,sheet F i ≠ 0 → 
      twain (C.buy c.Age) c.cab (lineS (forward c c.I.n) q i j) (lineS (forward c c.I.N) q i j):=by
  let P (q:ℕ)(C:Credit):Prop:=∀(c:CourseS H T fit e V W Z)(i j:Alma F),sheet F i ≠ 0 → 
    twain (C.buy c.Age) c.cab (lineS (forward c c.I.n) q i j) (lineS (forward c c.I.N) q i j)
  obtain ⟨B,seen⟩:=uniformPays (P:=P) (Finset.range (e+1))
    (fun q h=> WilsonPositionProgramTrialPublicJointFourActiveCourse.priced H T fit e V W Z simple q
      (Nat.le_of_lt_succ (Finset.mem_range.mp h)))
    (fun _ _ _ _ dom priced c i j hi=>(priced c i j hi).lift (dom _ c.I.warm) (trail_pos ..).le)
  exact ⟨B,fun c q h i j hi=>seen q (Finset.mem_range.mpr (by omega)) c i j hi⟩

def kept (Y:Coil F):Coil F:=fun i j=>if sheet F i=0 then 0 else Y i j

theorem read (Y:Coil F)(v:Verse F)(i:Alma F)(hi:sheet F i ≠ 0):
    (kept Y*ᵥv) i=(Y*ᵥv) i:=by simp [Matrix.mulVec,dotProduct,kept,hi]

theorem currency (H:Hol G)(T:SectionData F)(fit:4<D)(e:ℕ)(V W Z:Credit)(simple:G.Simple):
    ∃C:Credit,∀c:CourseS H T fit e V W Z,∀(X Y:Verse F)(A δ:ℝ),0 ≤ A → c.cab ≤ δ → 
      (∀q ≤ e,∀i,twain A δ (coeff q (X i)) (coeff q (Y i))) → 
      ∀q ≤ e,∀i:Alma F,sheet F i ≠ 0 → 
      let S:=c.vols
      twain (C.buy c.Age*A) δ
        (coeff q (street S.draws S.paid T fit c.I.n c.spur c.length X i))
        (coeff q (street S.draws S.paid T fit c.I.N c.spur c.length Y i)):=by
  obtain ⟨R,active⟩:=seats H T fit e V W Z simple
  obtain ⟨Q,clock⟩:=kinetics H T fit e V W Z
  let price:ℝ:=(∑_:Alma F,(e+1:ℕ)*(2:ℝ)) * ((e+1:ℕ)*2)
  refine ⟨(pur price).prodC (R.prodC Q),?_⟩
  intro c X Y A δ positive wide salary q depth i lit S
  let age:=c.Age
  let f t:=relativeF S.draws S.paid t c.spur c.length
  let M:=R.buy age
  let U:=Q.buy age
  let rate:ℝ:=(e+1:ℕ)*(2*U*1)
  have warm:1 ≤ age:=c.I.warm
  have rm:0 ≤ M:=zero_le_one.trans (R.purchase warm)
  have qm:0 ≤ U:=zero_le_one.trans (Q.purchase warm)
  have paid:0 ≤ δ:=(trail_pos ..).le.trans wide
  have op (l:ℕ)(ll:l ≤ e)(a b:Alma F):
      twain M δ (lineS (kept (forward c c.I.n)) l a b) (lineS (kept (forward c c.I.N)) l a b):=by
    by_cases unit:sheet F a=0
    · simpa [lineS,kept,unit] using ((twain.zero δ (V:=ℝ)).lift rm paid)
    · simpa [lineS,kept,unit] using (active c l ll a b unit).wide wide
  have tempo l (ll:l ≤ e) j:
      twain (rate*A) δ (coeff l (music (f c.I.n) X j)) (coeff l (music (f c.I.N) Y j)):=by
    exact musicFund _ _ U 1 A positive qm zero_le_one paid
      (fun a b ha hb=>(clock c a b ha hb).wide wide) X Y
      (fun a ha j=>by simpa only [one_mul] using salary a ha j) l ll j
  have posR:0 ≤ rate:=by unfold rate; positivity
  have fin:=cargo_rise _ _ M rate A positive rm posR paid op _ _ tempo q depth i
  rw [read _ _ i lit,read _ _ i lit] at fin
  apply fin.lift _ paid
  rw [Credit.products,Credit.products]
  apply mul_le_mul_of_nonneg_right _ positive
  apply le_trans _ (mul_le_mul_of_nonneg_right (pure_goal _ _) (mul_nonneg rm qm))
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  unfold price rate
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact le_of_eq (by ring)

end YM.Integration.WilsonPositionProgramTrialPublicJointFourActiveBudget
