import YM.Integration.WilsonRetainedOccupiedFiling

/-! Pay every old-action subword used by the partition logarithm on one
original Wilson coat, including the empty old subword of a fresh mark. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.OriginalMarkedRunAction
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure RGLocalTaylor
open Coat Matter Pond Blaze.March PhysicalNext.Repeat Greenbelt PhysicalNext.Repeat.Legato Work.F03 Bid
open PhysicalNext.Repeat.Malachite AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open Next.SectorChange WilsonCoherentMayerProjection Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Assembly
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoherentMayerHearing Dict06.Series
open Census Window
open scoped BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
    {P : Teller G} {Q : ConnectedActivityE6.Target G P} {W s μ C : ℝ} {o : Target.Order G W} {R : Rep G f}


variable {V : Type*}

def oldReading (X : Coat T F) (y : F.Slice G) (g p : ℝ)
    (a : PrismA G) (x : Site f) (z : Air f G) : ℂ :=
  (siteWeight a g p : ℂ)*sitePacket a.cells x ((X.wrapY y).input
    ((X.wrapY y).liftA (Comparison.RG02.Integral.temperature g) z))

def subwordTariff (T : Tube G S) (L : Side) (P : Teller G) (o : Target.Order G W)
    (s : ℝ) (X : Coat T F) (A : Finset V) (a : V → PrismA G) (σ D : V → ℝ)
    (g : ℝ) (K : ℕ) (B : Normal.poly (Eye X)) : ℝ :=
  let d := B.totalDegree+∑ j∈A, ((a j).rise+K+1)
  let fee := WilsonOriginalSignedSamplerMoment.fee T L P o d s
  let c := fun j r => occurrencePrice G L o.eta o.gap o.ample (σ j) (D j) (a j) r (A.card+1)
  let b := 1+Real.sqrt (Common.priced (1+payE o.eta o.gap o.ample (tubularPrice G L))
    (2*((A.card+1)*B.totalDegree)))
  Rise.coin B*((∏ j∈A, rootedSiteMass (a j) (σ j) (D j) K g)*|fee|+
    if A.Nonempty then b*((2:ℝ)^(A.card+1)*g^(K+∑ j∈A,(a j).grade)*
      ∏ j∈A,max (c j (a j).rise) (c j ((a j).rise+K))) else 0)

theorem occupied_subword (H : Cash W s μ L Q o C T R) (temp : 0≤Pressure.temp s)
    (χ : Chi) (v : Finset (LocalLTE.Fan.Veil c f)) (i : Greenbelt.Reserve S) (tag : S.Choices)
    (y : (Greenbelt.allot i).Slice G) (Z : SeriesA G) (K : ℕ) (A : Finset V)
    (σ D : V → ℝ) (hs : ∀ j∈A, 0<σ j) (filed : ∀ j∈A, Draw Z (σ j) (D j))
    (a : V → PrismA G) (member : ∀ j∈A, a j ∈ Z) (x : V → Site f)
    (g p : ℝ) (hg : 0<g) (small : g≤1) (lo : 1/2≤p) (hi : p≤3/2) :
    let F := Greenbelt.allot i
    let X := chamber T s o.K χ 1 v i tag
    ∀ B : Normal.poly (Eye X),
      let M := fun z : Air f G => Cloud.paint (fun j => z (tube X j)) B*
        ∏ j∈A, oldReading X y g p (a j) (x j) z
      let Kp := B*∏ j∈A,rootedSite X (a j) (x j) K g p
      Integrable M X.dice ∧ ‖(∫ z, M z ∂X.dice) -
        Cloud.wick (WilsonOriginalSignedSamplerMoment.ideal T F tag s)
          (WilsonOriginalSignedSamplerMoment.symmetry T F tag s) 0 Kp‖ ≤
        subwordTariff T L P o s X A a σ D g K B := by
  intro F X B M Kp
  by_cases hot : A.Nonempty
  · let n := A.card-1
    have cardA : n+1=A.card := Nat.sub_add_cancel (Finset.card_pos.mpr hot)
    let e : Fin (n+1) ≃ ↥A := (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using cardA.symm)).symm
    let pick := fun j => (e j : V)
    have inside (j) : pick j ∈ A := (e j).property
    have prodRead {Y : Type} [CommMonoid Y] (q : V → Y) :
        (∏ j : Fin (n+1), q (pick j)) = ∏ t∈A,q t := by
      have eq := e.prod_comp (fun t : ↥A => q t)
      exact eq.trans (by rw [Finset.univ_eq_attach]; exact Finset.prod_attach A q)
    have sumRead (q : V → ℕ) : (∑ j : Fin (n+1), q (pick j))=∑ t∈A,q t := by
      have eq := e.sum_comp (fun t : ↥A => q t)
      exact eq.trans (by rw [Finset.univ_eq_attach]; exact Finset.sum_attach A q)
    have paid := occupied_wick H temp χ v i tag y Z n K (fun j=>σ (pick j)) (fun j=>D (pick j))
      (fun j=>hs _ (inside j)) (fun j=>filed _ (inside j)) (fun j=>a (pick j))
      (fun j=>member _ (inside j)) (fun j=>x (pick j)) g p hg small lo hi B
    let old := fun (t : V) z => oldReading X y g p (a t) (x t) z
    let cost := fun j r => occurrencePrice G L o.eta o.gap o.ample (σ j) (D j) (a j) r (A.card+1)
    have number : n+2=A.card+1 := by omega
    have po (z : Air f G) := prodRead (fun t => old t z)
    have pm := prodRead (fun t=>rootedSite X (a t) (x t) K g p)
    have pw := prodRead (fun t=>rootedSiteMass (a t) (σ t) (D t) K g)
    have pc := prodRead (fun t=>max (cost t (a t).rise) (cost t ((a t).rise+K)))
    have sg := sumRead (fun t=>(a t).grade)
    have sr := sumRead (fun t=>(a t).rise+K+1)
    dsimp only [old, oldReading, X] at po
    dsimp only [X] at pm
    dsimp only [cost] at pc
    dsimp only [occupiedPolynomial] at paid
    simp only [number, po, pm, pw, pc, sg, sr] at paid
    simpa only [M, Kp, oldReading, subwordTariff, if_pos hot] using paid
  · have empty := Finset.not_nonempty_iff_eq_empty.mp hot
    subst A
    have manifest : X.manifest := by
      change (roster (LocalLTE.Fan.arm (S:=S) v)).flags=RG.flags (Pressure.temp s) (1:Config G c)
      rw [LocalLTE.Fan.Field.rosterD]
      exact (Greenbelt.prism T s χ o.K (1:Config G c) F).bowed temp
    obtain ⟨A,-,-,-⟩:=H.laws.data.localP F X rfl rfl manifest
    have typed := (WilsonCoherentMayerFuelSquare.sampled X A.fullC B).1
    have paid := WilsonOriginalSignedSamplerMoment.original T H temp χ v i tag B B.totalDegree le_rfl
    have nonneg : 0≤Rise.coin B := by rw [Rise.metal]; positivity
    have price := paid.trans (mul_le_mul_of_nonneg_left (le_abs_self _) nonneg)
    simpa [M,Kp,subwordTariff] using And.intro typed price

end YM.Integration.OriginalMarkedRunAction

