import YM.Integration.WilsonIndependentMatchedInheritedComparison

/-! A single funded course for the full inherited ordinary product at the true
older receiver and its fresh finite prior, on the computed reporting coordinates. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedInheritedHearing
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonIndependentMatchedReportedProxy (passport sectionSeal)
open WilsonIndependentMatchedRosterMasks (quiet choose)
open WilsonIndependentMatchedRosterPlanted (toll)
open WilsonIndependentMatchedRosterCuts (ranks)
open WilsonIndependentMatchedInheritedComparison (heard refund wage)
open WilsonIndependentMatchedInheritedCuts (Recorded)
open WilsonIndependentEvenPassport (old)
open scoped BigOperators Classical
variable {G:Gauge}{h D k e u₀ n:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}
    {p:h<D}{v:Rails h k u₀ e}{E W U V:Credit}
local notation "Cuts" => CutsP H T p v E W U V
local notation "Q" => fun _:Fin (n+1)=>sectionSeal T p

theorem original (run:XSpace.Run)(base u b:ℕ)(W₀ U₀ Ws Us:Credit)(cap η:ℝ)
    (nonneg:0 ≤ cap)(small:0<η)(width:u+b ≤ u₀)(stage:(n+1)*k ≤ b)
    (spread:1 ≤ (b:ℝ)-(((n+1)*h:ℕ):ℝ)-((n+1:ℕ):ℝ)/4):
    ∃C wallet:Credit,∀ᶠ idx:ℕ in atTop,∀(L:Torch H T p v E W U)(X:Fin (n+1)→Cuts)
      (f N:ℕ)(φ:Fin (n+1)→Rarity D)(a amp rent B:Fin (n+1)→ℝ)(stem:Fin (n+1)→TowerS G D)
      (y t z:ℝ)(o:CellR),
    (∀s,Recorded (X s) L run base idx f N (amp s) (run.step idx).spacing η (rent s) (stem s)) →
    (∀i ≤ old run base idx,L.L.V.y (f+i) ≤ cap) → L.L.V.anchor=f →
    SpringD L.L.V b u b W₀ → (∀flag:Fin (n+1)→Bool,Dormitory L.L.V (ranks flag k h) u U₀) →
    FramesR H L.L.V W V Q Us → SpringD L.L.V (capP Q) u (capP Q+2) Ws → Dormitory L.L.V (capP Q) u Us →
    0<t → (∀s s',s≠s' → ClearDay (φ s) (φ s') t) → (∀s,radiusH (φ s) 1 y ≤ z) →
    (∀s,0 ≤ rent s) → (∀s,Amplitude (φ s) (B s)) → ∀stop ≤ old run base idx,
    ∀(Z:ℝ)(upper N':ℕ),(X 0).ceilC ≤ upper → upper ≤ N → upper ≤ N' →
    Compar (X 0).ax.S (X 0).vesselsC.y (f+stop) (X 0).m ≤ Z → Bough Q φ y Z B →
    ∀j ≤ e,∀x:Fin 0→YForest G,
      ‖(heard X a φ stem (f+stop) y o).2 j 0 x-(refund X a amp φ N' (f+stop) y o).2 j 0 x‖ ≤
        (∑l∈Finset.univ.erase (quiet n),toll X (choose n l) b u (run.step idx).spacing η t z a amp rent B)+
        wage X a amp B C wallet (X 0).vesselsC.y Z upper:=by
  obtain ⟨C,wallet,price⟩:=WilsonIndependentMatchedBufferedVacuum.appointed H Q E W V Ws Us e u
  refine ⟨C,wallet,?_⟩
  filter_upwards [WilsonIndependentMatchedInheritedOrdinary.original (H:=H) (T:=T) (p:=p) (v:=v)
      (E:=E) (W:=W) (K:=U) (U:=V) run base u b W₀ U₀ cap η nonneg small width stage spread]
    with idx sold L X f N φ a amp rent B stem y t z o file ages anchor spring dorm frames spring' dorm' ht sep radius cash test stop smallStop
    Z upper N' buffer fine other room shape
  have courses (s:Fin (n+1)):(X s).vesselsC=L.L.V:=congrArg (fun l=>l.L.V) (file s).school
  have R₀:=courses 0
  have enrolled:HorizonP H (X 0).vesselsC W V Q:=fun _=>⟨passport (X 0)⟩
  have signed:=sold L X f N φ a amp rent B stem y t z o file ages anchor spring dorm ht sep radius cash test stop smallStop
  exact WilsonIndependentMatchedInheritedComparison.joined X a amp B φ stem (f+stop) upper N' _ Z y o
    (X 0).vesselsC.y (X 0).vesselsC.anchor C wallet
    (price (X 0).vesselsC (R₀ ▸ frames) enrolled (R₀ ▸ spring') (R₀ ▸ dorm'))
    (fun s=>(courses s).trans R₀.symm) (fun s=>(file s).report.trans (file 0).report.symm)
    (fun s=>congrArg₂ Nat.add ((file s).report.trans (file 0).report.symm) ((file s).gap.trans (file 0).gap.symm))
    (fun s=>(file s).top.trans (file 0).top.symm)
    (R₀ ▸ anchor ▸ Nat.le_add_right f stop)
    ((file 0).report ▸ Nat.add_le_add_left smallStop f) buffer ((file 0).top ▸ fine) other room shape signed

end YM.Integration.WilsonIndependentMatchedInheritedHearing
