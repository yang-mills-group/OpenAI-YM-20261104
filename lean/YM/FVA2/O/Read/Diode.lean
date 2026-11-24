import YM.FVA2.O.Read.Bulb
/-!
# Build invertible test data for the FAR profile matrix

`Declare`: a real base profile (not required non-negative) in positive time with
the appropriate reflected polarization coefficients. Reproduce the entire free point Gram
exactly with an appropriate such profile, hence positivity (and clearance).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Read
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Metric Real TopologicalSpace
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder
open FVA2.Scale MS.Rake MS.Theater Level O.Score LogTime MS.Plane MS.Heat MS.Tone Momentum Rake.Geo
open Equator Facets Dframe O.Enh O.Bind O.Project
variable { G:Gauge }{ I:Type }{n m k d:ℕ}{ s:Opens (Points 1) }{ V:Arenas G }{ A:Album G }
lemma Outside_open (d:ℕ): IsOpen ( Outside d ):= IsOpen.preimage (f:=outgoing) (Enh.continual continuous_const continuous_id) ( conf_open (1+d) ) -- use lemma
abbrev PlusV : Opens ( Points 1 ) := ⟨ Outside 1 ∩ {y:Points 1|0< y 0 timeAxis}, ( Outside_open 1 ).inter ( isOpen_lt ( g:=fun (y:Points 1)=>y 0 timeAxis ) continuous_const ( by fun_prop ) ) ⟩
lemma RootV : RootG∈PlusV:= by refine ⟨ ok_wall,?_ ⟩; change 0< nail timeAxis; simp [nail]
-- profiles: row=test, second index=length-T exterior label (of full alphabet), tensor combinations by finite linearity.
abbrev Exterior (m:ℕ):= { t:Test m // tsupport t ⊆ Outside m }
abbrev Geology (G:Gauge)(h:ℕ):= Toon G h→ Toon G h→ Exterior 1
lemma cover_c (t:RealU PlusV)(p:ℂ): tsupport (fun i=> p * ↑( t i )) ⊆ tsupport t:= by
    apply closure_minimal _ ( isClosed_tsupport _ ); intro i hi; by_contra! ht; have hv:= image_eq_zero_of_notMem_tsupport ht; exact hi ( by simp [hv] )
def crossU (t:RealU PlusV)(p:ℂ): Exterior 1:= by
    let f (i:Points 1):= p*(↑(t i):ℂ); have he : tsupport f⊆ Outside 1:= fun _ ht=> ( show _ ∈ Outside 1 ∩ _ from t.tsupport_subset ( cover_c t p ht ) ).1; exact ⟨⟨ f,ContDiff.mul contDiff_const ( Complex.ofRealCLM.contDiff.comp t.contDiff ), t.hasCompactSupport.of_isClosed_subset ( isClosed_tsupport _ ) ( cover_c t p ),fun _ ht=> Enh.room ( he ht ) ⟩,he⟩
lemma cross_b (t:RealU PlusV)(p:ℂ)(f:Points 1→ℂ): Test.applyTo (crossU t p).val f= p*money t f:= by unfold Test.applyTo money; rw [ ← integral_const_mul ]; apply integral_congr_ae; filter_upwards with x; change p*↑( t x )*f x=_; rw [ Complex.real_smul,mul_assoc ]
-- desired independence
abbrev G00 (A:Album G)(x:Points 1)(u v:Toon G d): ℂ:= coeff 0 ( lonelyG A x ( Dframe.flash u ) ( Single ( Dframe.flash v ) ) )
abbrev Portfolio (A:Album G)(H:Geology G d): Matrix (Toon G d) (Toon G d) ℂ:=fun b j=> ∑ i:Toon G d, ( H b i ).val.applyTo (fun x=> G00 A x j i )
lemma timeC (A:Album G)(h: Observed A)(u v:Toon G d): ContinuousOn (fun x=> G00 A x u v) (PlusV:Set (Points 1)):= ( h 2 _ 0 ).comp ( f:=fun x:Points 1=> outgoing x ) ( ( show Continuous ( outgoing (m:=1) ) from Enh.continual continuous_const continuous_id ).continuousOn ) (fun _ hp=>hp.1) -- syntax
local notation "A0"=> install V
lemma h_mu (h:Ground V)(he: Regular V)(u v:Toon G d) : G00 A0 RootG u v= Maxwell.Free.bond G 0 nail ( theory u ).val ( theory v ).val:= by
    let P:=Fin.append (Single ( flash u )) ( Single ( flash v )); have hp: Guarded P d := by intro i; induction i using Fin.addCases with| left i=> unfold P; rw [Fin.append_left]; exact size_le u | right i=> unfold P; rw [Fin.append_right]; exact size_le v
    rw [G00,lonelyG,party,scene_r h he hp (show _ from ok_wall), Normalize.screen,outgoing,RootG,Enh.lamp,Maxwell.Free.bond_eval ]; apply congr_arg; funext i; fin_cases i <;> rfl
abbrev Declare (t:RealU PlusV) (G:Gauge)(d:ℕ): Geology G d:= fun b p=> crossU t ( Score.coord p ( prism ( theory b ) ) )
lemma positiveV (h:Ground V)(he:Regular V)(hp:Observed A0)(d:ℕ): ∃ t:RealU PlusV, Portfolio A0 (Declare t G d) = GramP G d := by
    obtain ⟨t,hT⟩:= funds_R RootV ( F:=fun (i: Toon G d × Toon G d ) x=> G00 A0 x i.1 i.2 ) ( fun i=> timeC A0 hp i.1 i.2 ); refine ⟨ t,?_⟩; ext1 i b; unfold Portfolio GramP Declare; have h(i b:Toon G d): money t (fun x=> G00 A0 x i b )=G00 A0 RootG i b:= hT ( i,b ); simp_rw [cross_b,h,h_mu ( by assumption ) he ]; let v:= prism ( theory i ); change _= Maxwell.Free.bond _ _ _ ( theory b ).val v.val; conv_rhs=> rw [ ← all_sig v ]; rw [ AddSubmonoidClass.coe_finsetSum,map_sum ]; simp only [ SetLike.val_smul,map_smul ]; -- multiply.C.w.L
    rfl
lemma reserve (h:Ground V)(he:Regular V)(hp:Observed A0)(d:ℕ): ∃ g: Geology G d,H_pos ( Portfolio A0 g ):= by obtain ⟨t,ht⟩:= positiveV h he hp d; exact ⟨ Declare t G d, ht.symm ▸ GramP_pos ⟩
end YM.FVA2.O.Read
