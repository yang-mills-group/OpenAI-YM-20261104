import YM.XSpace.Molten
import YM.XSpace.Easel
/-!
# The point diagnostic IDENTIFIED with full continuum form for these actual labels!

 No position-tangent field reparam appears, even along unselected Spin3 tests. Cut must be sufficiently clearing (see `Manages` & `Granted` etc). But geometry otherwise arbitrary. No reliance on Ward formula with arbitrary R-linear field reads. NOTE labels unnormalized q=√2 * physical basis. Coupling extraction goes through next stage through tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Finale
open Function Filter Set Lattice Trace Chart2 Photo Cirrus Foundation Chiral Graph3 Stall Playpen Future Mu JetGauge Pages Next.Rank.Normal MvPolynomial Structure1 Normalize Relief AxesTangent Player Asymptotics Gland
open scoped Topology BigOperators InnerProductSpace Classical
variable {G:Gauge}(W:Initialize G)(g:G.Simple)(V:Store G){x y z:Cover}{ι:Type}{L:Filter ι}{a:ι→ℝ}
lemma sup_out (c:Shade.Cut)(p:ℝ)(i:PlaqAxes): Summable fun w:Cover=> outer W g c p x y z (w,i) :=by
  apply ((voice_adv W g c p x y z i).sub (profits W g x y z i)).congr; intro w; unfold state; rw [add_sub_cancel_right]
lemma fourth (c:Shade.Cut)(x y z:Cover)(a:ℝ): Graph3.receipt W g c a x y z= base a^14*( Seal W g x y z+ Graph3.bottom W g y z (tribute W c a x) + Graph3.supply W g x y z-∑ p:PlaqAxes, ∑' w:Cover,outer W g c a x y z (w,p)):=by
  unfold Graph3.receipt Seal; have he(p:PlaqAxes): (∑' w:Cover, state W g c a x y z (w,p))=(∑' w:Cover,outer W g c a x y z (w,p))+ ∑' w:Cover,mainQ W g x y z (w,p):= (sup_out W g c a p).tsum_add (profits ..); simp_rw [he,Finset.sum_add_distrib]; ring
-- supply has rank2 in the two open letters at U following the direct same-duality leak
variable {x y z:ι→Cover}{u v b:E4}{c:Shade.Cut}(t:Captain c L a x y z u v b)
local notation "J"=> Name G
local notation "M"=> mum W
local notation "Y"=> mrs W
include t in
lemma supply_a : funds L a 15 fun i=> ups W g (x i) (y i) (z i):=by
  unfold ups; refine IsBigO.sum (fun i (_:i∈Finset.univ)=> IsBigO.sum (fun j (_:j∈Finset.univ)=>?_)); unfold anomaly; simp_rw [Finale.solo W g]; refine gowns (j:=10) ((Y i).receipt (Y j) g t.turn rfl) ?_; refine IsBigO.sum (fun i' (_:i'∈Finset.univ)=> IsBigO.sum (fun j' (_:j'∈Finset.univ)=> IsBigO.sum (fun k (_:k∈Finset.univ)=>?_ ))); -- brace_move (RW loops)
  have h:= due (M j') (M i') g t.led t.hop.sec t.hop.sec (stake (brace_degree (W.surveys 4) false i 0)); refine (gowns (IsBigO.const_mul_left ((M k).starter (Y j) g t.hop.turn) (3*fuel i' j' k)) h).congr (fun a=>?_ ) (fun _=>rfl); unfold u_s; rw [brace_move (W.surveys 4) false i (y a)];rfl
include t in
lemma supply_g : Named L a 14 (fun i=> Graph3.supply W g (x i) (y i) (z i)) 0:= by unfold Graph3.supply; exact Named.low (minute t.led (IsBigO.add (supply_a W g t) (supply_a W g t.hop.turn)) (by decide)) t.led
include t in
theorem local_hour [NeBot L][L.IsCountablyGenerated] : Tendsto (fun i=> Graph3.receipt W g c (a i) (x i) (y i) (z i)) L (𝓝 (↑(Angle.answer c G u v b):ℂ)):=by
  simp_rw [fourth W g]; have he:= supply_g W g t; let f i:=Graph3.bottom W g (y i) (z i) (tribute W c (a i) (x i)); have hv:Named L a 14 f 0:= unpaid W g c t.led t.hop.both t.turn.turn.both (fun h=> Season.gap c t.turn.gleam.uv (sub_left_inj.mp h)) t.hop.gleam.uv.le t.turn.turn.gleam.uv.le
  have hh : Named L a 14 (fun i=>∑ j:PlaqAxes,∑' w:Cover,outer W g c (a i) (x i) (y i) (z i) (w,j)) (∑ i:PlaqAxes,(0:ℂ)):= Named.sum _ _ _ fun i _=>mainSe W g t i; simp only [Finset.sum_const_zero] at hh; simpa only [add_zero,sub_zero] using ((((sure W g t).add hv).add he).sub hh)
open Tornado
variable {x': Points 3} (H:Granted V 6 c)(K:Manages c G 6) (h:x'∈Good c 3)
include g H K h in
theorem status₁ : checked1 W V 6 x' (token G)=(↑(Angle.answer c G (x' 0) (x' 1) (x' 2)):ℂ):=by
  let x(j) i:= charts (n:=3) i j; have he : Captain c (Gate x') unit (x 0) (x 1) (x 2) (x' 0) (x' 1) (x' 2):= ⟨⟨stepG _,Eventually.of_forall unit_pos⟩,matched .., matched .., matched .., ⟨h 0 1 (by decide),h 0 2 (by decide),h 1 2 (by decide)⟩⟩; refine tendsto_nhds_unique (service W g V c x' h H K) ((local_hour W g he).congr fun i=>?_); rw [← costing W g _ _ _ _ _ (unit_pos i),← costing W g _ (unit i) _ _ _ (unit_pos i), show trip (loc 0 i) (loc 1 i) (loc 2 i)=_ from (landscape i).symm]; rw [show i.layout= (fun j=>Cirrus.home i+trip (x 0 i) (x 1 i) (x 2 i) j) from ?_,adequate,adequate,reply_plus,blossom_plus]; funext j; unfold x charts; fin_cases j <;> simp [trip]
end YM.XSpace.Finale
