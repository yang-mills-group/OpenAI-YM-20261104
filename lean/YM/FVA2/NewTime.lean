import YM.FVA2.Foil
/-!
# A genuine scaling path. Integer- and small-change-of-measurement interpolation are
not needed because the supplied MS_Data has log scale y at all μ: install this kernel law.
We keep ℝ parameters; exact reference height log ν can shift by constant as needed.
Prove by fv MoonB.Connected & bouquet. Polynomial control elsewhere.
-/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.FVA2.Waves
open MS Koszul
open MS.Puff MS.Puff.Engine MS.Puff.SplitP MS.Puff.Actors MS.Puff.Mom MS.Book.Convolve
open MS.Plane MS.Land MS.Tone MS.Rake MS.Rake.Geo MS.Vane MS.Tide MS.Port MS.Menus
open Function Filter Set MeasureTheory Real
open MS.Tide MS.Tide.PeakT MS.Dial MS.SpaceOut
open Maxwell.Free Pert.Position
open scoped Topology BigOperators ContDiff
variable {I W:Type*}
variable {W:Type}{G:Gauge}{B:MS.Local.Physical.Deck G}{O:Booked B}(M:MS_Data G O){s:ℝ}[LinearOrder W](w:W→ Rake.Label B){x:W→MS.Tone.QP}(h:Injective x)(S:Finset W)(n:ℕ) (v y:ℝ)
include h
omit [LinearOrder W] in
lemma moved_pin : Mesh (frameF Unit v) (fun p (_:Unit)=> x p):= by
   intro i j hi; have he:0<‖x i-x j‖:= norm_pos_iff.mpr (sub_ne_zero.mpr (h.ne hi)); refine ⟨⟨_,he,fun i=>?_⟩,⟨_,he,fun i=>?_⟩⟩ <;> simp [Rake.Geo.roots]
lemma gathered (i:Unit) : Vane.Allow (Dial.spine M w v x S n) i:= by
   obtain hp := Dial.pin M w v h; rcases S.eq_empty_or_nonempty with hh|hh; rw [hh, hp.1 ]; exact (Fleet.allow_zero i).1; exact ( Dial.reports _ ( moved_pin h v ) hp hh n ).1 i
open MS.Rake (Mesh)
omit h [LinearOrder W] in
lemma widened (a:ℝ)(x:W→ MS.Tone.QP)(h:Injective x): Injective (fun i=> exp a • x i):= fun _ _ he=> h ( smul_right_injective _ (exp_pos _|>.ne') he )
lemma direct : Dial.book M w v (fun p=> exp y • x p ) S n= Port.τ (-(Vane.charge ( Label.h ∘ w ) S:ℤ)) y* Dial.book M w (v+y) x S n:= by
    obtain hs:= Dial.pin M w ( v+y ) h; apply congr_fun (Port.MoonB M (σ:=fun _=>y) (P:=frameF Unit v) (fun i=>rfl) hs ( Dial.pin M w v ( widened y x h ) ) S n ( gathered M w h S n ( v+y ) ) ) ()
-- code general Tether: Geo.θ expires if scale negative! ν abs. use τ version.Tank
open MS.Fleet MS.Puff
abbrev δ (w:W→ℕ)(s:Finset W)(y:ℝ):= Port.τ ( -( Vane.charge w s :ℤ ) ) y
omit h
def tether (y:ℝ)(w:W→ℕ) : Linear ( Finset W→ MS.Book.Convolve.T ℂ ) (Finset W→ MS.Book.Convolve.T ℂ ) where
   toFun v S:= (δ w S y) • (v S)
   map_add' _ _:= funext (fun _=> smul_add ..)
   map_smul' v _:= funext (fun _=> smul_comm _ v _)
lemma allowedT (w:W→ℕ) : Tether ( tether y w ) (Trunk.stack ( marked W )) (Trunk.stack (marked W)):= by
       refine ⟨ funext fun p=>?_,fun x y'=>funext fun u=>?_⟩
       · change (δ w p y) • ( marked W ).refineV Trunk.unit p =( marked W ).refineV Trunk.unit p; unfold refineV; split
         next h=> rw [ h ]; simp [δ,Vane.charge,Port.τ, marked]
         next _ => exact smul_zero _
       change (δ w u y) • (( marked W ).Lift Trunk.core x y' u)=( marked W ).Lift Trunk.core _ _ u; simp_rw [SplitP.loan,Finset.smul_sum]; refine Finset.sum_congr rfl fun j hj=>?_ ; change _= Trunk.core ( (δ w j.1 y) • _ ) ( (δ w j.2 y) • _ ); obtain ⟨ha,hb⟩:= MS.Puff.SplitP.joins.mp hj; rw [ show (δ w u y)= _ from (by unfold δ Vane.charge; rw [ T_add, ← ha, Finset.sum_union hb ]; push_cast; ring_nf : (δ w u y)=(δ w j.1 y)*(δ w j.2 y)),map_smul,map_smul, LinearMap.smul_apply, mul_smul, smul_comm ];
include h
lemma tour_time (Gg: Finset W) : Dial.tour M w v (fun p=>exp y • x p) Gg n= Port.τ (-(Vane.charge ( Label.h ∘ w ) Gg:ℤ)) y * Dial.tour M w (v+y) x Gg n:= by
   let V0:= Dial.book M w (v+y) x; let X:= Label.h ∘ w; let J:=tether y X; let L:= Trunk.stack ( marked W ); change L.cheers _ Gg.card _ _= J ( L.cheers V0 Gg.card ) _ _; rw [ Tether.cheersV ( allowedT y X ) ]; apply congrArg (fun U=> L.cheers U Gg.card Gg n); exact funext fun s=> funext fun n'=> Waves.direct M w h s n' v y -- direct pins ground
end YM.FVA2.Waves
