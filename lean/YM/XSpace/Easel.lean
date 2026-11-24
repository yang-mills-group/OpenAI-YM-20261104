import YM.XSpace.Tornado
/-!
# The full power-ren diagnostic atm before frontier. Recheck against these actually stronger limiting problems (but equivalent to evaluating T/c)

This compares its raw and positioned 3-point read, with counterterm handling complete at positive g order (still need nonzero test value; pricing the limit here). Unnormalized b, U (§tri basis with q before divide √2). **Not** yet smearing or coupling registration. Lower-piece always silent from the compensated b cluster. Orientation independent, centered σ shape not assumed symmetric. No assumption substituting projections into norm comparison at measurable fields. No exact theory in this file.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Tornado
open Function Set Filter Lattice Trace Chart2 Maxwell Maxwell.Free Maxwell.Wick Photo Cirrus Foundation Chiral Graph3 Stall Playpen Future Mu JetGauge Pages Next.Rank.Normal MvPolynomial Structure1 Normalize Relief AxesTangent
open scoped Topology BigOperators InnerProductSpace Classical
variable {G:Gauge}(W:Initialize G)(g:G.Simple)(V:Store G)(c:Shade.Cut)(w: Points 3)(h:w∈Good c 3) (H:Granted V 6 c) (S:Manages c G 6)
abbrev value : ℂ:= checked1 W V 6 w (token G)
include g h H S in
lemma service : Tendsto (fun i : Cirrus.Sample 3=> receipt W g c (unit i) (loc 0 i) (loc 1 i) (loc 2 i)) (Gate w) (𝓝 (value W V w)):=
  (removes W V 6 (token G) c S H w h gust (fun i he=> ignored W g w (beyond_conf c h) i he)).congr fun i=> by rw [← costing W g c _ _ _ _ (unit_pos i), ← show i.layout=_ from landscape i]
def netBill (a:ℝ)(z x y:Cover):= receipt W g c a z x y-base a ^14* bottom W g x y (tribute W c a z)
include g h H S in
lemma registered : Tendsto (fun i : Cirrus.Sample 3=> netBill W g c (unit i) (loc 0 i) (loc 1 i) (loc 2 i)) (Gate w) (𝓝 (value W V w)):=by
  have he:= unpaid W g c (s:= ⟨stepG w,Eventually.of_forall unit_pos⟩) (flight w 1 0) (flight w 2 0) (by intro f; exact (show Injective w.ofLp from beyond_conf c h).ne (by decide : (1:Fin 3) ≠2) (sub_left_inj.mp f)) (le_of_lt (h 1 0 (by decide))) (le_of_lt (h 2 0 (by decide)))
  have hh:=(service W g V c w h H S).sub he; rw [sub_zero] at hh; exact hh
end YM.XSpace.Tornado
