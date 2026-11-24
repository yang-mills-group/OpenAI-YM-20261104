import YM.Integration.FVA1Physical.Wilson.IteratedBankStep

/-! Finite arbitrary-depth iteration of the distributed independent normalized
Wilson prescription on identical physical histories, before choosing the
period, cutoff, forest, tag or support test. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix MvPolynomial Lattice RG YM.Wilson Exterior Tree Precision
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Bout MSbar.Duel MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Rolling MSbar.CrossH MSbar.Measuring
open PhysicalNext.Repeat.Legato Push.Uniform MSbar.Midpoint MSbar.Bakery.Film
open Extra.Iteration Push.PriceCompiler PhysicalNext.Repeat.Roost Next.Foundations
open scoped Classical Topology BigOperators
variable {G:Gauge}

def orbitDegree (p m:ℕ) : ℕ→ℕ
  | 0 => m
  | d+1 => bankDegree p (orbitDegree p m d)

private theorem orbitDegree_pos (p:ℕ) {m:ℕ} (hm:1 ≤ m) (d:ℕ) : 1 ≤ orbitDegree p m d := by
  cases d with
  | zero => exact hm
  | succ n => change 1 ≤ _*(p+1+p)+2;omega

def bankOrbit (R:PhysicalNext.Repeat.Legato.Run G) {n r:ℕ} (N:ℕ) (S:Scene R.family.path.levels n r)
    (fs:∀ j,Forest (R.family.path.levels.clock.op j n).ratio)
    (vs:∀ j,(R.family.path.levels.clock.op j n).Choices) (p m:ℕ)
    (T:∀ j,Nesting G (R.family.path.levels.S.side j n)) : ℕ → ∀ j,Nesting G (R.family.path.levels.S.side j n)
  | 0,j => T j
  | d+1,j =>
      let A:=sceneIssue (N:=N) (RunFormalChain.fromRun R) S (fs j) (vs j)
      let prev:=bankOrbit R N S fs vs p m T d (j+1)
      emittedRows A R.metals.O (inheritedBank A (orbitDegree p m d) (S.action (j+1)) prev) p

theorem BankPaid.weaken {c:Side} {b:Site c} {y ε η:ℝ} {s p m:ℕ} {T:Nesting G c}
    (paid:BankPaid b y s p m ε T) (hy:1 ≤ y) (ordered:ε ≤ η) : BankPaid b y s p m η T := by
  intro i hi
  exact ⟨(paid i hi).1,Quote.widen (paid i hi).2 (Real.rpow_le_rpow_of_exponent_le hy ordered) le_rfl⟩

theorem all_fixed_bank_orbits (simple:G.Simple) (R:PhysicalNext.Repeat.Legato.Run G) (u:G.ColorIndex)
    (V:Voice G) (cle:Clear G V) (frame:R.metals.O=chart G)
    (invoice:iteratedBankInvoice u V cle simple R.metals R.rolls R.alloy R.kit)
    (r p m s d:ℕ) (pr:p ≤ r) (hm:1 ≤ m) (hs:6 ≤ s) {η:ℝ} (hη:0<η) :
    ∃ δ:ℝ, 0<δ ∧ ∀ᶠ k:ℕ in atTop,∀ N n,∀ (S:Scene R.family.path.levels n r),
      Realized R.alloy.B.kin N n k r (Lis.sun G u) S → ∀ j,k ≤ j → j+d<N →
        ∀ (fs:∀ i, Forest (R.family.path.levels.clock.op i n).ratio)
          (vs:∀ i,(R.family.path.levels.clock.op i n).Choices)
          (b:∀ i,Site (R.family.path.levels.S.side i n)) (T:∀ i,Nesting G (R.family.path.levels.S.side i n)),
          (∀ i,j ≤ i → i<j+d → (R.family.path.levels.clock.op i n).ratio.embed (b i)=b (i+1)) →
          let θ:=R.family.path.levels.clock.hatBeta
          BankPaid (b (j+d)) (θ (j+d)) s p m δ (T (j+d)) →
          BankPaid (b j) (θ j) s p (orbitDegree p m d) η (bankOrbit R N S fs vs p m T d j) := by
  induction d generalizing η with
  | zero => exact ⟨η,hη,.of_forall fun _ _ _ _ _ _ _ _ _ _ _ _ _ => id⟩
  | succ d ih =>
    obtain ⟨ℓ,small⟩ := margin_eventually (half_pos hη)
    let q:=orbitDegree p m d
    obtain ⟨δ,positive,prev⟩:=ih (bankSlack_pos p q ℓ)
    refine ⟨δ,positive,?_⟩
    filter_upwards [prev,inherited_bank_step simple R u V cle frame invoice r p q s ℓ pr (orbitDegree_pos p hm d) hs]
      with k old step
    intro N n S scene j kj jN fs vs b T embed θ input
    have eqn : j+1+d=j+(d+1) := by omega
    have oldinput : BankPaid (b (j+1+d)) (θ (j+1+d)) s p m δ (T (j+1+d)) := by rw [eqn]; exact input
    have mid := old N n S scene (j+1) (by omega) (by omega) fs vs b T
      (fun i lo hi=>embed i (by omega) (by omega)) oldinput
    have emb := embed j le_rfl (by omega)
    let A:=sceneIssue (N:=N) (RunFormalChain.fromRun R) S (fs j) (vs j)
    let oldT:=bankOrbit R N S fs vs p m T d (j+1)
    have inc:BankPaid (A.S.ratio.embed (b j)) (θ (j+1)) s p q (bankSlack p q ℓ) oldT := by
      change BankPaid ((R.family.path.levels.clock.op j n).ratio.embed (b j)) _ _ _ _ _ _
      rw [emb];exact mid
    have out:=step N n S scene j kj (by omega) (fs j) (vs j) (b j) oldT inc
    exact out.weaken (R.family.path.levels.fits.delayed j).le (by linarith only [small])

end YM.Integration.FVA1Physical.Wilson
