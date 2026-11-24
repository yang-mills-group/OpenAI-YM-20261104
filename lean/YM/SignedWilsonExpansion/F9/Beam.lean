import YM.SignedWilsonExpansion.F9.ProbeRank

/-!
# Invoice for point beams. Cloister, pre- and post-charge on just the
activated horizons. Use `probe`, zeros at the projected rank only, retain
all earlier shelf prices. Includes zero rank.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{h p k k₀ m N u e i j l r q:ℕ}{F:Labels.Frame G h}{H:Hol G}
variable {a x b c B M X:ℝ}{L:Cloister G h}{S:Ample h u r}

abbrev prebound (H:Hol G)(F:Frame G h)(S:Ample h u r)(L:Cloister G h) :=
   let d:= h+1
   backL d * peak H F u r S L.lamp.preD L.lamp.s L.lamp.anger * coinL d
abbrev propel (H:Hol G)(F:Frame G h)(S:Ample h u r)(L:Cloister G h)(e:ℕ) := (pump_gain H F u r e S L).choose
abbrev chime (G:Gauge)(e u k r:ℕ):= (delta_price k e r u G).choose
abbrev render (L:Cloister G h)(k e u r:ℕ):= (((delta_price k e r u G).choose_spec h L)).choose
structure Bill (H:Hol G)(F:Frame G h)(S:Ample h u r)(L:Cloister G h)(k e:ℕ)(x:ℝ): Prop where
   begins : prebound H F S L / ((inkPin L).patch.L.val:ℝ) ≤ Real.exp (-Real.log (inkPin L).patch.L.val/2)
   known : propel H F S L e≤ x
   thermal : render L k e u r ≤ x
-- annuity after election; all realm inputs controlled in its age only
variable {E W:Credit}{R:Realm G (q+1) E}

/-- PointStep prices on the actual E age -/
abbrev clear (H:Hol G)(F:Frame G h)(S:Ample h u r)(L:Cloister G h): Prop:=prebound H F S L / ((inkPin L).patch.L.val:ℝ) ≤ Real.exp (-Real.log (inkPin L).patch.L.val/2)

def annuity (G:Gauge)(h k e r q u:ℕ)(F:Frame G h)(E W:Credit): Credit :=
   let C:= ((costXV G q E).powC (chime G e u k r)).prodC W
   (E.powC h).prodC ((C.plus ((pur (rowCost F u r)).prodC C)).plus W)
lemma cash_nn (R:Realm G q E)(L:Credit){m:ℕ}(hx:R.anchor≤m):0≤R.cash L m:= zero_le_one.trans (L.purchase (R.depth _ hx))
private lemma reel_illum {I J:Gear G}{a:Stand I}{b:Stand J}(k:ℕ)(hp:I=J)(z:HEq a b)(Y:Bookend ℝ G): sunI I a k Y=sunI J b k Y:=by subst J; rw [eq_of_heq z]

/-- Connect the at-history Cloister to the actual rally, without casting the point-step weights. -/
lemma appears (H:Cloister G h)(hi:R.anchor≤m)(p:e≤q)(g:m<N)(t:relight R.draws R.paid m (R.mint m hi) H):
    ∃ U:Rally (e+1) 0 (inkPin H), Nonempty (Courant H U.P) ∧ U.x=R.cash (costXV G q E) m ∧
      ∀ k (Y:Era G ℝ), (verseI R.draws R.paid m N k Y).2=sunI (inkPin H) U.P k Y.2:=by
    let U:= ReelTime R p hi g (le_refl N) (le_refl N)
    obtain ⟨V,hv,_,hb,_⟩:= launchW U t.1.symm
    refine ⟨V,t.2 N g R.hG R.green V.P hv,hb,fun k Y=>?_⟩; exact reel_illum k t.1.symm hv.symm Y.2

abbrev eng (R:Realm G q E)(h m:ℕ):ℝ:= ((R.draws.S.block m).val:ℝ)^h
abbrev rollFrac (A:Levels G)(m:ℕ):ℝ:= Real.exp (-(PathCost.arc A.S m)/2)
lemma rollFrac_pos (A:Levels G)(m:ℕ):0<rollFrac A m:=Real.exp_pos _
lemma rollFrac_le (A:Levels G)(m:ℕ):rollFrac A m≤1:=Real.exp_le_one_iff.mpr (by linarith [PathCost.arc_nn A.S m])
lemma eng_nn (R:Realm G q E)(h m:ℕ):0≤eng R h m:=by unfold eng; positivity
abbrev ClockPage (R:Realm G q E)(m h k N:ℕ)(Y:Era G ℝ) := pointStep R.draws R.paid m N h k Y
lemma funds_zero (S:Ample h u r)(H:Hol G)(F:Frame G h)(hi:R.anchor≤m)(p:e≤q)(g:m<N)(t:relight R.draws R.paid m (R.mint m hi) L)
    (w:Bill H F S L k e (R.cash W m))(Y:Era G ℝ)(z:Auth k Y)(a Z:ℝ)(en:0≤a)(s:Earlier Y e r u a)
    (y:Fruit 0 1 u (Y.2 e r) Z)(sh:∀ j:TagIx F r,row F (Y.2 e r) j=0):
    let M:=R.cash (annuity G h k e r q u F E W) m; let C:=(ClockPage R m h k N Y).2 e r
    Fruit 0 1 u C (rollFrac R.draws m * Z + M*a) ∧ ∀ j:TagIx F r, ‖row F C j‖ ≤ M*a:=by
    obtain ⟨U,⟨f⟩,hb,hu⟩:= appears L hi p g t
    intro M C; let I:=inkPin L; let F':=verseI R.draws R.paid m N k Y; let K:=pump (Y.2 e r) (owns _ U.P.M)
    let l:ℝ:= (R.draws.S.block m).val; let O:=R.cash W m; let A:=render L k e u r*U.x^(chime G e u k r); let D:=l^h
    obtain ⟨hf,hy⟩:= (pump_gain H F u r e S L).choose_spec.2 _ f Y k Z a z en s sh y; let B:=propel H F S L e
    have hx:Fruit 0 1 u (F'.2 e r-K) (A*a):=by unfold F'; rw [hu]; exact ((delta_price k e r u G).choose_spec h L).choose_spec.2 U f _ _ z en s
    have he:0≤l:=by unfold l; positivity
    have hg:0≤D:=pow_nonneg he _
    have hp:D≤R.cash (E.powC h) m:= by unfold cash; rw [Credit.power]; exact pow_le_pow_left₀ he (R.taxes m hi).height _
    have ht : C=D • F'.2 e r:=rfl
    have vl: (inkPin L).patch.L.val=(R.draws.S.block m).val:=congr_arg (fun i:Gear G=>i.patch.L.val) t.1
    have hA:0≤ A:= mul_nonneg (((delta_price k e r u G).choose_spec h L).choose_spec.1) (pow_nonneg (zero_le_one.trans U.rich) _)
    have hB:0≤ B:= (pump_gain H F u r e S L).choose_spec.1
    let I':=chime G e u k r; let V':=((costXV G q E).powC I').prodC W; let X:= R.cash (pur (rowCost F u r)) m; let V:= R.cash V' m
    have hX:rowCost F u r≤ X:=pure_goal (rowCost F u r) _
    have hE:A≤ V:= (mul_le_mul_of_nonneg_right w.thermal (pow_nonneg (zero_le_one.trans U.rich) I')).trans_eq (by unfold V V' cash; rw [Credit.products,Credit.power,hb]; exact mul_comm ..)
    let P0:= rowCost F u r; have hP:0≤ P0:=rowCost_nn F
    have hR: A+P0*A+B ≤ R.cash ((V'.plus ((pur P0).prodC V')).plus W) m:= by
        have hS:P0*A≤ R.cash ((pur P0).prodC V') m:= by unfold cash; rw [Credit.products]; exact mul_le_mul hX hE hA (hP.trans hX)
        exact (add_le_add ((add_le_add hE hS).trans (Credit.fuel _ _ (R.depth _ hi))) w.known).trans (Credit.fuel _ _ (R.depth _ hi))
    have hM:D*(A+P0*A+B)≤ M:=by unfold M cash annuity; simp only [Credit.products]; exact mul_le_mul hp hR (by positivity) (hg.trans hp)
    have hcost: D*(prebound H F S L*speck (inkPin L).patch^(h+1))≤ rollFrac R.draws m:= by
        have vh:= w.begins; unfold rollFrac; rw [arch]; rw [vl] at vh; refine le_trans (le_of_eq ?_) vh; unfold D l speck; rw [vl]; rw [pow_succ,inv_pow]; field_simp
    let hh:= hx.plus hf zero_le_one; -- rewrite tensors
    rw [sub_add_cancel] at hh
    constructor
    · rw [ht]; apply (hh.μ D).more; rw [abs_of_nonneg hg]; change D*(A*a+(prebound H F S L*speck I.patch^(h+1)*Z+B*a))≤ _
      rw [show D*(A*a+(_*Z+B*a))= (D*(prebound H F S L*speck I.patch^(h+1)))*Z+D*(A+B)*a by ring]
      exact add_le_add (mul_le_mul_of_nonneg_right hcost y.C) (mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left (add_le_add_left (le_add_of_nonneg_right (mul_nonneg hP hA)) _) hg).trans hM) en)
    intro j; have hc:= row_bound F _ hx S.floor j; rw [row_sub F _ _ hh hf S.floor] at hc
    rw [ht,row_μ,norm_smul,Real.norm_of_nonneg hg]; have hW: ‖row F (F'.2 e r) j‖ ≤ (P0*A+B)*a:= by rw [add_mul, mul_assoc]; exact sub_le_iff_le_add.mp ((norm_sub_norm_le ..).trans hc) |>.trans (add_le_add_right (hy j) _)
    exact (mul_le_mul_of_nonneg_left hW hg).trans ((le_of_eq (mul_assoc ..).symm).trans (mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left (by rw [add_assoc]; exact le_add_of_nonneg_left hA) hg).trans hM) en))
lemma purchased_front (S:Ample h u r)(H:Hol G)(F:Frame G h)(hi:R.anchor≤m)(g:m<N)(t:relight R.draws R.paid m (R.mint m hi) L)
    (Y:Era G ℝ)(hY:Auth k Y)(p:∀j,r<j→Y.2 0 j=0)(i:r≤k)(d:ℕ)(he:d≤h)
    (hh:∀ j:TagIx F r,(F.grades j.val).1 < d→ row F (Y.2 0 r) j=0)(v:TagIx F r)(cost:(F.grades v.val).1≤d):
      row F ((ClockPage R m h k N Y).2 0 r) v=((R.draws.S.block m).val:ℝ)^(h-(F.grades v.val).1)*row F (Y.2 0 r) v:=by
    obtain ⟨U,⟨f⟩,hb,hu⟩:= appears L hi (Nat.zero_le _) g t
    let V:=verseI R.draws R.paid m N k Y; let a:=(F.grades v.val).1
    have ha:= through0 H F U f Y V hY (Auth.verse R.draws g R.hG R.green hY) (hu ..) p i d he hh v cost
    change row F (eng R h m • V.2 0 r) v=_; rw [row_μ,ha,smul_eq_mul,← mul_assoc]; apply congr_arg (· * _)
    change eng R h m * speck (inkPin L).patch^a= _; rw [show eng R h m=((inkPin L).patch.L.val:ℝ)^h from ?_,lux (inkPin L).patch (cost.trans he)]; all_goals
       simp only [t.1]; rfl
end YM.WilsonCoeffUV.Mer.Xa
