import YM.Integration.FVA1Physical.Wilson.IteratedBankGate

/-! A repeatable coefficient estimate for the full independent Wilson step
on a single realized trajectory. The input and output are on successive
native tori and have the same rooted norm through their entire degree. -/
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

def iteratedBankInvoice (u:G.ColorIndex) (V:Voice G) (cle:Clear G V) (simple:G.Simple) : Qlocal.Schedule.Goal G :=
  fun M D A X=>Qlocal.Schedule.vacuumInvoice u V M D A X ∧
    Qlocal.Schedule.selectedThreshold (G:=G) (inheritedBankMenu V cle simple) M D A X ∧
    Qlocal.Schedule.mapThreshold (railMenu simple) M D A X

theorem bankInvoice_obtainable (u:G.ColorIndex) (V:Voice G) (cle:Clear G V) (simple:G.Simple) :
    Qlocal.Schedule.Obtainable (iteratedBankInvoice u V cle simple) :=
  (Qlocal.Schedule.vacuumInvoice_obtainable simple u V cle).also
    ((Qlocal.Schedule.selectedThreshold_obtainable (G:=G) (inheritedBankMenu V cle simple)).also
      (Qlocal.Schedule.mapThreshold_obtainable (G:=G) (railMenu simple)))

/-- The scene's action at j+1 was the genuine reset of that finer block.
All realized scenes and all admissible forests share the estimate. -/
theorem inherited_bank_step (simple:G.Simple) (R:PhysicalNext.Repeat.Legato.Run G) (u:G.ColorIndex)
    (V:Voice G) (cle:Clear G V) (frame:R.metals.O=chart G)
    (invoice:iteratedBankInvoice u V cle simple R.metals R.rolls R.alloy R.kit)
    (r p m s ℓ:ℕ) (pr:p ≤ r) (hm:1 ≤ m) (hs:6 ≤ s) :
    ∀ᶠ k:ℕ in atTop,∀ N n,∀ (S:Scene R.family.path.levels n r),
      Realized R.alloy.B.kin N n k r (Lis.sun G u) S → ∀ j,k ≤ j → j+1<N →
        ∀ (F:Forest (R.family.path.levels.clock.op j n).ratio) (v:(R.family.path.levels.clock.op j n).Choices),
          let A:=sceneIssue (N:=N) (RunFormalChain.fromRun R) S F v
          let θ:=R.family.path.levels.clock.hatBeta
          ∀ (b:Site A.c) (T:Nesting G A.f),
            BankPaid (A.S.ratio.embed b) (θ (j+1)) s p m (bankSlack p m ℓ) T →
            BankPaid b (θ j) s p (bankDegree p m) (2*margin ℓ)
              (emittedRows A R.metals.O (inheritedBank A m (S.action (j+1)) T) p) := by
  have growth : Tendsto (fun j=>(R.alloy.B.a.params j).order) atTop atTop := by
    apply tendsto_atTop.2;intro i
    filter_upwards [eventually_ge_atTop (R.t i)] with j ready
    exact (Nat.le_succ i).trans (((R.makes.stages i).2 j ready).1)
  have estate:=invoice.1.1 growth
  have ch:=(R.bought R.T R.tuning.receipts R.t R.accepts R.stories R.doors R.makes R.carries R.books).1
  have merit:=townsR R.b R.Q R.T R.t R.stories R.doors ch
  let d:=bankDegree p m
  let demand:=r+p+m+s+ℓ+d
  filter_upwards [Alto.skyline R.alloy.B r simple estate.levy merit s u hs,
    eventually_ge_atTop (R.t demand)] with k skyline delayed
  intro N n S scene j kj jN F v A θ b T paid i hi
  let Z:=RunFormalChain.fromRun R
  let H:=R.family.path.levels.params j;let H':=R.family.path.levels.params (j+1)
  let src:=inheritedBank A m (S.action (j+1)) T
  have high:demand ≤ H.order:=(Nat.le_succ demand).trans (((R.makes.stages demand).2 j (delayed.trans kj)).1)
  dsimp only [demand] at high
  have jN' : j < N:=by omega
  have kj':k ≤ j+1:=by omega
  have branch:A.S.patch.Branches A.S.kernel G:=(R.family.path.levels.blocks j n).branches
  have gate:inheritedBankGate V cle simple H H' A.S.patch A.S.kernel p m s ℓ ≤ θ j:=
    (inheritedBankGate_le V cle simple H H' _ _ (by omega) (by omega) (by omega) (by omega)).trans (invoice.2.1 j n)
  rw [inheritedBankGate,dif_pos branch,dif_pos hm] at gate
  have use:=(eventually_atTop.mp (inherited_field_rows V cle (chart G) (chart_ok G) simple H H' A.S.patch
    A.S.kernel branch p m d s hm (margin_pos ℓ))).choose_spec _ gate
  have season:=auditorium R.b R.Q R.T R.t R.stories R.doors ch V N n j jN' simple estate.sees
    (fun t=>invoice.1.2.1 _ _ (R.alloy.B.valid.pays t) _ (step_paid R.alloy.B.a t))
  have bill:=use A (A.S.ratio.embed b) rfl rfl season
  have rail:=railMenu_covers simple R.metals.K H H' A.S.patch A.S.kernel (by omega:s ≤ H.order)
    (by omega:ℓ ≤ H.order) (x:=θ j) (invoice.2.2 j n)
  have hY:tip G A.S.patch.L (θ j)=θ (j+1):=(Extra.Iteration.block_beta (a:=R.family.path.levels) j).symm
  dsimp only at rail bill
  rw [hY] at rail
  rw [hY,←frame] at bill
  have bud:=(scene.budget (j+1) jN' kj').1
  have funds := skyline N n S scene
  have w:=funds.1 (j+1) kj' jN'
  have wed:Alto.Wedge A.T Alto.Dean (hatW (θ (j+1))) (Alto.cWidth (θ (j+1))) s p :=
    ⟨fun t ht=>w.shares t (ht.trans pr)⟩
  have expan : Expanse A.T 1 p := ⟨fun t ht=>bud.plane.profile t (ht.trans pr)⟩
  have unit := (scene.step (j+1) jN kj').choose_spec.choose_spec.1
  have pocket:=bill bud.bond expan wed T (S.action (j+1)) unit
    (fun t ht=>funds.2 (j+1) kj' jN t (ht.trans pr))
    (fun t ht=>⟨paid.through _ ht,(paid t ht).1⟩) i hi
  have prem:Premier (main A.f A.pre.clip A.pre.path):=by
    change Premier (main _ (R.family.path.rep N n (j+1)).clip (R.family.path.rep N n (j+1)).path)
    rw [Z.clips N n (j+1) jN',Z.selected N n (j+1) jN'];exact bud.quiet
  have crit:Critical A.F A.pre.clip A.pre.path A.ρ:=by
    change Critical F (R.family.path.rep N n (j+1)).clip (R.family.path.rep N n (j+1)).path _
    rw [Z.clips N n (j+1) jN',Z.selected N n (j+1) jN'];exact (Z.planned.critical N j n jN' F).1
  have pd:(mold A.pre A.F A.v).PosDef:=by
    change (Push.Uniform.block (priced F v (R.family.path.rep N n (j+1)).clip (R.family.path.rep N n (j+1)).path) 0).PosDef
    rw [Z.clips N n (j+1) jN',Z.selected N n (j+1) jN']
    exact blueprint F v (Z.kin.path N (j+1)) _ branch bud.quiet (Z.post.price _) (Z.planned.gap N j n jN' F)
  constructor
  · change (PowerSeries.coeff i (emittedRows A R.metals.O src p)).totalDegree ≤ d
    rw [emittedRows,PowerSeries.coeff_map]
    exact (Rolling.clearD ..).trans (normalized_input_degree A R.metals.O src p m hm bud.bond pd expan
      (fun t _=>inherited_bank_degree A m t (S.action (j+1)) T) hi)
  have zero:bulkPoint A 0=0:=by rw [stationary_point A branch prem crit pd,smul_zero];exact map_zero _
  have raw:Vault (address A.F G) {A.S.ratio.embed b} (αm (θ (j+1))) s d (bulkPoint A 0)
      (PowerSeries.coeff i (normalizedRows A R.metals.O src p)) (θ (j+1)^margin ℓ):=by rw [zero];exact pocket
  have moved:=emitted_rows A R.metals.O src p i s d branch prem crit pd b 0 rail.1 rail.2.2.1
    (selected_land R jN' S F v s rail.1 rail.2.1) raw
  simp only [smul_zero] at moved
  exact Quote.widen moved (rail.2.2.2 d (by omega)) le_rfl

end YM.Integration.FVA1Physical.Wilson
