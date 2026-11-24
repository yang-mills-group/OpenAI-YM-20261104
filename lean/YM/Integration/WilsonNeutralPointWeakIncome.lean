import YM.Integration.WilsonNeutralPointWeakDated
import YM.Integration.WilsonPointChildInverseIncome

/-! At the original physical scale one pair of tariffs controls every
ultraviolet birth and every sequence of individual child positions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralPointWeakIncome
open FormalBulk08 Matrix Laurent Precision Exterior PowerSeries Lattice RG Wilson Tree Stationary
open Push.Uniform Bloch Reef Jets Orb Wick Flat Next.Free UVExtension.Free
open Function Filter Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove Dove.Lab
open Quire Palm Grail Chapel Borough Sable Tundra Aster Clover Series Work.F03 Work.F05 Work.F08
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels PhysicalNext.Repeat.Legato Next.Foundations
open WilsonNeutralPointWeakSchool WilsonNeutralPointWeakYears WilsonNeutralPointWeakDated
open WilsonPointChildInverseIncome WilsonPointChildNormalizedWidth
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{d D:ℕ}(R:Run G)(wood:Primer.Families R.family)(a:hue G)(depth:d<D)(o:Loc G 1)
variable {U:ℕ→ℕ}(simple:G.Simple)(formal:WilsonWindowFormalPurchase.Canonical U R.kit)
variable (strong:WilsonNeutralPointForecast.Filed R.kit)(weakly:WilsonNeutralPointWeakForecast.Filed R.kit)
local notation "F" => R.family.labels.level d
local notation "A" => R.family.path.levels

private theorem forget {o:Loc G 1}{d r:ℕ}{t:Tile (edgeL G) r}{b:ℝ}
    (h:Knoxville (grain (fame _) 1) d (0,o) t b):Knoxville (fame _) 0 (0,o) t b:=by
  simpa only [Knoxville,Gorge.shine,zero_mul,Real.exp_zero] using penn_shrink h (Nat.cast_nonneg _)

include simple formal strong weakly in
theorem original (E:ℕ):Weak R wood a depth o E ∧ Forward R wood a depth E:=by
  obtain ⟨k,large⟩:=eventually_atTop.1
    (WilsonNeutralPointWeakDated.original (w:=0) (E:=E) R wood depth simple formal strong weakly)
  let X:Type:=({N:ℕ // k≤N} × (∀j,Site (R.family.S.block j)))
  let Z:=campus R X wood k
  let C:Pin Z.scrolls:=⟨fun x=>x.1.val,fun x=>x.1.property⟩
  let digits (x:X):∀j,Site (R.family.S.block j):=x.2
  obtain ⟨rows,matrices⟩:=large k le_rfl X C a o digits
  let Catalog:=Letter F × Fin (E+1) × Fin (d+E+1)
  have offers (c:Catalog):∃b:Deck C→ℝ,Soft (sage C) b ∧ (∀i,0≤b i) ∧
      ∀(i:Deck C)(p:Studio D),Knoxville (fame _) 0 (0,o)
        (field R wood depth C a digits i c.1 p c.2.1.val c.2.2.val) (b i*‖p‖):=by
    obtain ⟨b,hs,hp,paid⟩:=rows c.1 c.2.1.val (Nat.le_of_lt_succ c.2.1.isLt) c.2.2.val
    refine ⟨b,hs,hp,fun i p=>?_⟩
    simpa only [one_mul] using forget (paid i p)
  choose b soft nonneg tested using offers
  let total (i:Deck C):ℝ:=∑c:Catalog,b c i
  have wage:Soft (sage C) total:=soft_bill Finset.univ fun c _=>soft c
  have pays (i:Deck C)(c:Catalog):b c i≤total i:=Finset.single_le_sum (f:=fun s=>b s i)
    (fun s _=>nonneg s i) (Finset.mem_univ _)
  have room (j:ℕ):max 1 (ageZ ((A).clock.hatBeta j))≤RG16.Lambda A j:=(WilsonPointChildWidthPurchase.prices R formal j).2.2.2
  constructor
  · obtain ⟨M,h,hM,pay⟩:=wage
    refine ⟨max 1 M,h,le_max_left ..,?_⟩
    filter_upwards [eventually_ge_atTop k] with j jk N jN digit
    let route:X:=(⟨N,jk.trans jN⟩,digit)
    let i:Deck C:=⟨⟨route,j,jk⟩,jN⟩
    have power:((sage C).day i)^h≤(RG16.Lambda A j)^h:=pow_le_pow_left₀ ((sage C).good i) (room j) _
    have cap:total i ≤ max 1 M*(RG16.Lambda A j)^h:=(le_abs_self _).trans ((pay i).trans
      (mul_le_mul (le_max_right ..) power (pow_nonneg ((sage C).good i) _) (zero_le_one.trans (le_max_left ..))))
    refine ⟨mul_nonneg (zero_le_one.trans (le_max_left ..)) (pow_nonneg (zero_le_one.trans ((le_max_left 1 _).trans (room j))) _),?_⟩
    intro v p l hl r hr
    let c:Catalog:=(v,⟨l,Nat.lt_succ_of_le hl⟩,⟨r,Nat.lt_succ_of_le hr⟩)
    exact (tested c i p).mono (mul_le_mul_of_nonneg_right ((pays i c).trans cap) (norm_nonneg _))
  · intro v y e he
    obtain ⟨M,h,hM,pay⟩:=matrices y v e he
    refine ⟨M,h,hM,?_⟩
    filter_upwards [eventually_ge_atTop k] with j jk N jN digit
    let route:X:=(⟨N,jk.trans jN.le⟩,digit)
    let i:Turn C:=⟨⟨route,j,jk⟩,jN⟩
    exact (pay i).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ((tide C).good i) (room j) _) hM)

include simple formal strong weakly in
theorem funded (E:ℕ):WilsonPointChildWidthHistory.Income R wood a depth o E:=by
  obtain ⟨weak,forward⟩:=original R wood a depth o simple formal strong weakly E
  exact WilsonPointChildInverseIncome.income R wood a depth o simple formal weak forward

end YM.Integration.WilsonNeutralPointWeakIncome
end
