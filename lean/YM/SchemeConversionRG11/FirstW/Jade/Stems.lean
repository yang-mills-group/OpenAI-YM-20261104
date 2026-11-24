import YM.SchemeConversionRG11.FirstW.Fade.Ports
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter Set MeasureTheory Metric Lattice Pert Align Topology Maxwell Next.Rank.CellsInt
open scoped BigOperators Classical
variable {T:Itinerary}{E:Type} [NormedAddCommGroup E][NormedSpace ℝ E] {G:Gauge}
variable {A: Sight T G} {f:Hall T E}{S:Set E4} {n:Side} {j:ℕ}
lemma sets_supply (j:ℕ)(a:Fin j→Axis) (p:Site n→E)(x:Site n): combine (List.ofFn a) p x = ∑ s:Finset (Fin j), Bare.sign s • p (stop x (Bare.walk a s)) := by
 have he(D:List Axis)(z:Cover): combine D (fun v:Cover=>p (x+wrap n v)) z=combine D p (x+wrap n z):= by
    induction D generalizing z with
    | nil=> rfl
    | cons i D ih=> simp only [combine,up,ih,map_add,wrap_step]; rw [add_assoc]
 have H:= (he (List.ofFn a) 0).symm; rw [map_zero,add_zero,←jumps_eq,jumps_supply] at H; rw [H]; refine Finset.sum_congr rfl fun s _=>?_ ; rw [zero_add,Bare.displaced,map_sum]; simp
lemma shifts_add (f:Hall T E)(a:Fin j→Axis): surface (List.ofFn a) f=fun i x=> (T.gap i^j)⁻¹ • ∑ s:Finset (Fin j), Bare.sign s • f i (stop x (Bare.walk a s)):=funext fun i=>funext fun x=> by rw [surface,Pi.smul_apply, List.length_ofFn,sets_supply]
-- diagonal spire, path concatenation unrestricted. lean Finset order arbitrary.
lemma curved_plus {X:Type*}[AddCommGroup X][One X](x:Four X)(i j:Walk)(A:Wind G X) : swerve x (i++j) A A=swerve x i A A + swerve (stop x i) j A A + G.ad (rail x i A) (rail (stop x i) j A) := by
 induction i generalizing x with
 | nil=> simp [swerve,stop, rail]
 | cons a i ih=> rw [List.cons_append]; simp only [stop,swerve_eq,ih,rail_plus,rail, LinearMap.add_apply,map_add]; abel
lemma goodbye {X:Type*}[AddCommGroup X][One X](x:Four X)(i:Walk)(A:Wind G X): swerve (stop x i) (Lattice.reverse i) A A= -swerve x i A A:= by
 induction i generalizing x with
 | nil=> simp [swerve,stop,Lattice.reverse]
 | cons a i ih=>
   rw [show Lattice.reverse (a::i)= Lattice.reverse i ++ [a.rev] from by simp [Lattice.reverse],curved_plus]; simp only [stop,ih,reverse_stop,rail_reverse]; simp only [swerve_eq,rail, back_step]; simp only [LinearMap.zero_apply,add_zero,back_step,map_zero,map_neg,LinearMap.neg_apply,neg_neg,swerve]; rw [ad_for (rail (x+a.vec) i A)]; abel
lemma patched_q {X:Type*}[AddCommGroup X][One X](x:Four X)(w:Walk)(A:Wind G X)(i j:Axis): swerve x (patch w i j) A A= swerve (stop x w) (square i j) A A + (2:ℝ) • G.ad (rail x w A) (rail (stop x w) (square i j) A) := by
 unfold patch; rw [curved_plus,curved_plus,rail_plus]; simp only [stop_append, square_stop,rail_reverse,goodbye, map_add,map_neg,LinearMap.add_apply,ad_diag0]; rw [ad_for (rail (stop x w) (square i j) A), two_smul]; abel
lemma pleased_lim (h:Pleased T S f)(hx:(0:E4)∈S): Helen (fun i=> f i 0):=by obtain ⟨Y,h⟩:=h; exact ⟨_,h.identity id tendsto_id 0 hx 0 sails_zero⟩
-- leading rail decomposition along a walk; differences. Flat sum leading subtract.
def towerStep (T:Itinerary)(w:Walk)(f:Hall T E): Hall T E:= fun i x=> f i (stop x w)
def straks (T:Itinerary)(w:Walk)(f:Hall T E) : Hall T E:=fun i x=> (T.gap i)⁻¹ • (f i (stop x w)-f i x)
lemma unwalking (w:Walk)(h:Pleased T S f): Pleased T S (towerStep T w f):= by induction w with
 | nil=> exact h
 | cons i w ih=> have H:= ih.by i.vec; rw [mail_vec] at H; exact H
lemma verst (w:Walk)(h:Pleased T S f): Pleased T S (straks T w f):= by
 induction w with
 | nil=> rw [show straks T [] f=0 from funext fun i=>funext fun x=> by simp [straks,stop]]; exact ⟨0,Score.untouched⟩
 | cons i w ih=> have H:= ih.by i.vec; rw [show straks T (i::w) f =mailR T (straks T w f) i.vec+slipC T f i from funext fun j=>funext fun x=>by simp [straks, slipC,stop,mail_vec,← smul_add]]; exact H.enclose (h.slip _)
def cubeCost (n:Side)(w:Walk)(A:FullT G n)(x:Site n): G.Color:= (w.map fun s=> flareL s • A (x,s.dir)).sum -- for pos steps
lemma walk_away (a:Fin j→Axis)(s:Finset (Fin j))(A: FullT G n)(x:Site n): cubeCost n (Bare.walk a s) A x = ∑ v∈s,A (x,a v) := by
 unfold cubeCost Bare.walk; simp only [List.map_map,comp_def,posDir,flareL, Bool.false_eq_true,↓reduceIte,one_smul]; rw [← List.sum_toFinset _ s.nodup_toList,s.toList_toFinset]
 -- alternative
lemma slateE (j:ℕ)(a:Fin j→Axis)(s:Finset (Fin j))(h:HatP T S A): Pleased T S (fun i x=> (T.gap i)⁻¹ • (rail x (Bare.walk a s) (A i)-cubeCost _ (Bare.walk a s) (A i) x)) := by
 have he (w:List (Fin j)): Pleased T S (fun i x=> (T.gap i)⁻¹ • (rail x (w.map fun k=>posDir (a k)) (A i)-cubeCost _ (w.map fun k=>posDir (a k)) (A i) x)):= by
    induction w with
    | nil=> simp only [List.map_nil,rail,LinearMap.zero_apply,cubeCost,List.sum_nil,sub_self,smul_zero]; exact ⟨0,Score.untouched⟩
    | cons i w ih=>
      let p:=posDir (a i); let W:=w.map fun k=>posDir (a k); simp only [List.map_cons]
      have e(k:ℕ)(x:Site (T.period k)): rail x (p::W) (A k)- cubeCost _ (p::W) (A k) x = (rail x W (A k)-cubeCost _ W (A k) x) + (rail (x+p.vec) W (A k)-rail x W (A k)) := by
         simp only [rail,LinearMap.add_apply,boardAt,p,posDir,LinearMap.smul_apply,LinearMap.proj_apply, Step.used,cubeCost, List.map_cons,List.sum_cons,flareL]; simp
      change Pleased T S (fun k x=>_ • (rail x (p::W) (A k)-cubeCost _ (p::W) (A k) x)); simp_rw [e,smul_add]; exact ih.enclose ((walkP h W).slip p)
 exact he _
end YM.RG11.FirstW
