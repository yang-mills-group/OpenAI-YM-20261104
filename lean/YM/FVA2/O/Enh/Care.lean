import YM.FVA2.O.Enh.Above
/-!
# First (unsmeared) test for the rank of the free OPE Gram

Observer at unit distance from origin. Weight **exactly** d in the output; pair with
all labels through the horizon d, prove detection on these tests (`reader`). See also
`O/Read/Point` about the square reflected Gram through the whole horizon.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Enh
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Metric Real
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix
open FVA2.Scale MS.Rake MS.Theater Level O.Score LogTime MS.Plane MS.Heat MS.Tone Momentum Rake.Geo
open Equator Facets Dframe
variable {G:Gauge}{ I:Type }{n m k d:ℕ}{x: Points n}{v:ℝ}
variable { V:Arenas G }
abbrev Ground (A:Arenas G): Prop:= ∀ i, StarGround ( A i )
local notation "BΩ"=> Press.portDeck G
local notation "A0"=> install V
lemma scene_r (hp:Ground V)(he:Regular V){p:Scan G n}(ht:Guarded p d)(h:x∈conf n): coeff 0 ( install V n x p )= scene x d ( tape p ht ):= by rw [ caring p ht he h ]; rw [ test,Reg.Point.story,coeff_mk,hp ]
abbrev nail := basis timeAxis
abbrev RootG : Points 1:= points fun _=> nail
lemma lamp (x:E4): forest (0:Points 1) ( points (fun _ : Fin 1=> x) )= pairPoints 0 x:= by ext1 i; fin_cases i <;> rfl
lemma ok_wall : RootG∈ Outside 1:= by
    change outgoing RootG∈ conf 2; rw [outgoing,RootG,lamp]; exact pair_ok (fun h=>by have hp:= basis_norm timeAxis; change ‖nail‖=1 at hp; rw [← h, norm_zero ] at hp; norm_num at hp )
lemma season_t (q:Toon G d)(u:Grade G d): Guarded ( Fin.append (Single (own u)) (Single (Dframe.flash q)) ) d:= by
    intro i; induction i using Fin.addCases with| left j=> rw [ Fin.append_left ]| right j=> rw [ Fin.append_right ]; exact Dframe.size_le q
lemma twigs (hp:Ground V)(he:Regular V)(i:Toon G d)(v:Grade G d): coeff 0 ( lonelyG A0 RootG ( own v ) ( Single ( Dframe.flash i ) ) )= Maxwell.Free.bond G 0 nail ( vertex v ).val ( Dframe.theory i ).val:= by
    rw [ lonelyG,party,scene_r hp he (season_t i v) (show _ from ok_wall), Normalize.screen, outgoing,RootG,lamp,Maxwell.Free.bond_eval ]; apply congr_arg; funext i; fin_cases i <;> rfl
abbrev NOW (A:Album G)(p:Toon G d)(i:Grade G d):= coeff 0 ( lonelyG A RootG ( own i ) (Single ( Dframe.flash p )) )
def detect (V:Arenas G) (d:ℕ): (Grade G d→ℂ) →ₗ[ℂ] Toon G d→ℂ :={
    toFun F q:= ∑ i:Grade G d,F i*NOW (install V) q i
    map_add' f g:= by funext i; simp only [Pi.add_apply,add_mul, Finset.sum_add_distrib]
    map_smul' a f:= by funext i; simp [ Finset.mul_sum,mul_assoc ] }
lemma tactile (h:Ground V)(he:Regular V)(d:ℕ): LinearMap.ker ( detect V d )=⊥:= by
    rw [ Submodule.eq_bot_iff ]; intro v hv; let x:=∑ i:Grade G d,v i • vertex i; have hx(i:Toon G d): Maxwell.Free.bond G 0 nail x.val ( theory i ).val=0:= by
        obtain h:=congr_fun ( LinearMap.mem_ker.mp hv ) i; change ∑ q:Grade G d,v q* NOW ( install V ) i q=0 at h; simp_rw [NOW,twigs (show Ground V from by assumption) he] at h; unfold x; rw [AddSubmonoidClass.coe_finsetSum,map_sum,LinearMap.sum_apply]; simp_rw [SetLike.val_smul,map_smul,LinearMap.smul_apply ]; exact h
    have hp : x.val=0:= by refine Maxwell.Free.pair_nonzero timeAxis _ (r:=1) zero_lt_one x.property (fun q ht=> ?_ ); rw [← Maxwell.Free.pair_flow _ _ nail,neg_smul, one_smul,show -basis timeAxis+nail=0 from neg_add_cancel _,zero_add ]; let t:Sec G d:=⟨ q,ht ⟩; change Maxwell.Free.bond _ _ _ _ t.val=0; nth_rw 1 [ ← all_sig t ]; simp only [AddSubmonoidClass.coe_finsetSum,map_sum,SetLike.val_smul,map_smul,hx,smul_zero, Finset.sum_const_zero ]
    funext i; obtain he : paygrade i x=v i:= by
       unfold x; rw [map_sum, Finset.sum_eq_single i]; · rw [_root_.map_smul,pivotA,if_pos rfl,smul_eq_mul,mul_one];
       · intro j hj h; rw [ _root_.map_smul,pivotA,if_neg h.symm,smul_zero];
       simp
    rw [← he, show x=0 from Subtype.ext hp, map_zero ]; rfl
lemma reader (h:Ground V)(he:Regular V){f:Grade G d→ℂ}(hv:∀ b: Toon G d,∑ i:Grade G d,f i * NOW (install V) b i= 0): f=0:= by apply ( Submodule.mem_bot ℂ ).mp; rw [ ← tactile h he d ]; exact LinearMap.mem_ker.mpr ( funext hv )
end YM.FVA2.O.Enh
