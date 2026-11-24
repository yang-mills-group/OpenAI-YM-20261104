import YM.GradedFar.Round.Astral
/-!
# RoundMeter value, in terms exactly of G.9 at any fixed cap(s)
-/
namespace YM.FVA2.GradedFar.Physical.Round
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh Moving Growth Pose Books Scale Dframe
open Continuation Continuation.Window
open OPE Orbits Logged
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n m h k j t p : ℕ} {I V:Type} {d : Fin n → ℕ}{e: Fin m→ℕ} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple} {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
variable {R : Family G} {f : Extraction.Order} {P : Table R.book}
    (U : Spec.Final R f P) (J K : FramesH P)
    (E : (d:ℕ)→ℝ→FieldEnd G d) (Y : (d:ℕ)→ℝ→ Prediction G d) (θ:ℝ→ℝ)
    (Q : Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
    (W : Bookshelf N U J K E Y θ) (D : Earned N M U J K θ) (hD:oriented U K)
    (ht: LogTrace U Q.port) (he:∀ h:ℕ,∀ᶠ r in τ, ∀ u : Sec G h,K r h u=J r h (E h r u))
    (hGrid : Grid N U J)
variable {C B:ℝ}(hC:0<C)(hB:0<B)
local notation "Q₀"=> upper G C B
local notation "Γ"=>windows Q₀
local notation "g₀"=>gYM G ∘ Window.len
include H
-- `Y0` vs painted and row vs boundary; common cap readout
lemma regimen {w:Continuation.Window}{x:Points n}{y:Points m}(hp:forest x (squeeze (-w.sep) y)∈conf (n+m))(u:Inputs G d)(v:Inputs G e)(hd:∀ i,d i≤ h)(he:∀ i,e i≤ h):
     row N x u y v w.sep= boundary N (Fin.append (installedInputs hd u) (installedInputs he v)) (along w x y) := by
    ext1 k; rw [coeff_row (ℓ:=h) H x u y v w.sep hd he hp k]; unfold along; rw [← wide_here]; unfold boundary shop Reg.Point.story; rw [coeff_mk,Scale.Jury.fxt,dif_pos hp]

omit H in
lemma named_cap {w:Continuation.Window}{x:Points n}{y:Points m}(hp:w.len • (along w x y) ∈conf (n+m))
    (o:View U)(u:Inputs G d)(v:Inputs G e)(hd:∀ i,d i≤h)(he:∀ i,e i≤h)
    (hx:∀ i,K w.len h (up (hd i) (u i))= U.sector.derivatives.rise (hd i) (K w.len _ (u i)))
    (hy:∀ j,K w.len h (up (he j) (v j))=U.sector.derivatives.rise (he j) (K w.len _ (v j))):
    Y0 U K d e w o x y u v=painted U K o.1 (fun _:Fin (n+m)=>h) w.len (along w x y) (Fin.append (installedInputs hd u) (installedInputs he v)) := by
   rw [Y0_value]; change _= painted U K o.1 _ _ (forest x (w.Stretch • y)) _
   rw [← record U K o w x y (installedInputs hd u) (installedInputs he v) hp, Y0_value]
   rw [show here K w.len (d:=fun _:Fin n=>h) (installedInputs hd u)= _ from funext hx,
     show here K w.len (d:=fun _:Fin m=>h) (installedInputs he v)= _ from funext hy]; symm
   apply Subtable.indebted U _ hd he
   have hh:atPos w.Coarse o.2 y= atPos w.len o.2 (w.Stretch • y) := funext (fun i=> (by unfold atPos Window.Coarse; rw [mul_smul];rfl))
   rw [hh,show beside (atPos w.len o.2 x) (atPos w.len o.2 (w.Stretch • y))=atPos w.len o.2 (along w x y) ∘ finSumFinEquiv from funext fun i=> by cases i <;> simp [atPos,along]]
   exact Function.Injective.comp (fun _ _ h=> hp (show (w.len • along w x y) _=(w.len • along w x y) _ from add_left_cancel h)) finSumFinEquiv.injective
-- orientation pay for inclusion price
omit H in
lemma cup {d e:ℕ}(h:d≤e)(L:ℝ) : ∃ D:ℝ,∀(u:Sec G d), Ball L u→ Ball D (up h u) := by
   let V : RowSpace G d →L[ℂ] RowSpace G e:= LinearMap.toContinuousLinearMap ((chair G e).toLinearMap ∘ₗ up h ∘ₗ (chair G d).symm.toLinearMap)
   let B:=max L 0; have hL:0≤B:=le_max_right ..
   refine ⟨‖V‖*B,fun u hu=> (chair_ball _ (by positivity)).mpr ?_⟩
   rw [show chair G e (up h u)=V (chair G d u) from (by simp [V])]
   exact (ContinuousLinearMap.le_opNorm ..).trans (mul_le_mul_of_nonneg_left ((chair_ball u hL).1 (fun j=> (hu j).trans (le_max_left ..))) (norm_nonneg _))
omit H in
lemma hosts (d:Fin n→ℕ)(L:ℝ)(h:∀ i,d i≤t) : ∃ D:ℝ,∀(u:Inputs G d),Within L u → Within D (e:=fun _=>t) (installedInputs h u) := by
   choose C hc using fun i=> cup (G:=G) (h i) L
   obtain ⟨D,hD⟩:= Finite.bddAbove_range C
   exact ⟨D,fun u hu j l=> (hc j _ (hu j) l).trans (hD (Set.mem_range_self j))⟩
include W D ht he hD hGrid
set_option maxHeartbeats 400000 in
/-- **(G.9) value part**, on same real (H) fields as everywhere. This was derived from
prior physical (C5/LogTrace etc.) budgets. Not asserting derivative versions here,
period posterior estimates, Epoch, or the existence of the purchased stocks. See `Grid`.
-/
theorem rounded_world : SourceCost N U K θ := by
   intro n m d e p X Y' hX hx hY hy B C hB hC L R
   obtain ⟨h,hK⟩:= Finite.bddAbove_range d; obtain ⟨t,hT⟩:= Finite.bddAbove_range e
   let h':=6+h+t; have hp:6≤h':=by unfold h'; omega
   have hd i:d i≤h':= le_trans (hK (mem_range_self _)) (by show h≤6+h+t; omega)
   have hr i:e i≤h':= le_trans (hT (mem_range_self _)) (by show t≤6+h+t; omega)
   let I:=Continuation.Window × View U × XSet X Y' × {u:Inputs G d // Within L u} × {v:Inputs G e // Within R v}
   let w (i:I):= (i.1 : Continuation.Window); let o (i:I):=i.2.1; let S (i:I):=i.2.2.1; let u (i:I):=i.2.2.2.1.val; let v (i:I):= i.2.2.2.2.val
   have hu i:Within L (u i):= i.2.2.2.1.property; have hv i: Within R (v i):= i.2.2.2.2.property
   obtain ⟨R0,hR⟩:= hosts (G:=G) d L hd; obtain ⟨R1,h1⟩:=hosts (G:=G) e R hr
   let P i:=Fin.append (installedInputs hd (u i)) (installedInputs hr (v i)); let M':= max R0 R1
   have he0 (i:I): Within M' (e:=fun _=>h') (P i) := by
      intro j; induction j using Fin.addCases with
      | left j=> unfold P; rw [Fin.append_left]; exact fun q=> (hR _ (hu i) j q).trans (le_max_left ..)
      | right j=> unfold P; rw [Fin.append_right]; exact fun q=> (h1 _ (hv i) j q).trans (le_max_right ..)
   let T':= windows (upper G C B); let f:=comap w T'; let r i:= (w i).len; have hf:Tendsto w f T':= tendsto_comap
   have hx':∀ᶠ i in f,∀ (j:Fin n),∀v:Sec G (d j), K (r i) h' (up (hd j) v)= _ := eventually_all.mpr (fun j=> ((windows_short _).comp hf).eventually (hD.raises _ _ (hd j)))
   have hy':∀ᶠ i in f,∀ (j:Fin m),∀v:Sec G (e j), K (r i) h' (up (hr j) v)= _ := eventually_all.mpr (fun j=> ((windows_short _).comp hf).eventually (hD.raises _ _ (hr j)))
   let b':= Duly (upper G C B) f w hf simple
   have H' : Bill b' (p+1) 0 (fun i=> Y0 U K d e (w i) (o i) (S i).1 (S i).2 (u i) (v i)-crop p (θ (w i).len)
       (row N (S i).1 (u i) (S i).2 (v i) (w i).sep)) := by
      apply (precision N M H U J K E Y θ Q W D hD ht he hGrid hC hB f w hf hX hx hY hy o S hp p P M' (Eventually.of_forall he0)).apply_eq
      filter_upwards [hx',hy',((windows_separation _).comp hf).eventually (eventually_conf hX hx hY hy),((windows_short _).comp hf).eventually self_mem_nhdsWithin] with i hx hy hz (hi:0<r i)
      have he:= hz.1 _ (S i).1.property _ (S i).2.property
      rw [regimen N M H he _ _ hd hr]; rw [Function.comp_apply, wide_here] at he
      rw [named_cap U K (present hi he) _ _ _ hd hr (fun j=>hx j _) (fun j=> hy j _)]; rfl
   obtain ⟨C',hC',a,H'⟩:= H'
   refine ⟨C',hC',a,?_⟩; filter_upwards [eventually_comap.mp H'] with t ht o x hx y hy u hu v hv
   have he:=ht ((t,o,(⟨x,hx⟩,⟨y,hy⟩),⟨u,hu⟩,⟨v,hv⟩):I) rfl
   rw [post,neg_zero,zero_mul,exp_zero,mul_one] at he; exact he
end
end YM.FVA2.GradedFar.Physical.Round
