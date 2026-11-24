import YM.IntegrationR2.Rose.Word
import YM.FullVolume.Table.Salute
import YM.Source.Preservation
/-!
# Already assembled log prices and same-chart motion at top.

This E comparison uses FULL forced, keeps paid cylinder and real kernel &
launch denominator. No smallness assumption transfers automatically to alter
chosen curve values or rules; the producer here is for top replacement only.
No matching inferred after a step from this estimate alone.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonStartup.Rose
open Function Filter RG Wilson Lattice Design Work Ac Padded Start
open scoped ContDiff Topology Matrix.Norms.Frobenius Classical
open Ovens Ovens.Pipes Quad.Rose Progress.DirectedRecipe Rack
open YM.FullVolume.Urns PhysicalNext.Repeat Set
variable {G : Gauge} {n : Side} {b : BudgetPoint} {θ:ℕ} {v w β a ε:ℝ}
variable {c:Clip} {M:Berry G θ} {W:PathData G}
section joint
local notation "P"=> dictionary G n
abbrev original (n:Side)(W:PathData G)(c:Clip)(b:BudgetPoint)(β:ℝ):= finish W c b (dictionary G n) (Start.payload c b G n β) β 0
abbrev sketch (n:Side)(W:PathData G)(c:Clip)(b:BudgetPoint)(β:ℝ)(M:Berry G θ):= finish W c b (dictionary G n) (city M n b c β) β 0
local notation "O"=> original n W c b β
local notation "X"=> sketch n W c b β M
abbrev toll (n:Side)(M:Berry G θ)(c:Clip)(β:ℝ) : Code G n:= (Rack.widen (dictionary G n) (Rose.raw M c n β)).regular
abbrev area (n:Side)(M:Berry G θ)(b:BudgetPoint)(c:Clip)(β:ℝ):= issue b (toll n M c β,0)
local notation "KK"=>area n M b c β
lemma toll_cash (hp: θ> 2)(he:(Rose.payload M n c β).EBound b ε): Cash b ((KK).E,0) ε 0:=by
   let h:= preserves P (raw M c n β) b; have ht:=(h.regular (Rose.regularFamily (b:=b) (n:=n) M hp c β)); have hh := h.Ebound he; have hz := (ticket0 G n b).2.1
   refine ⟨⟨ht.smooth,ht.at_flat,ht.vanish⟩,⟨hz.sym,hz.symtest,hz.meas,hz.meas_test,hz.reads,hz.reads_test,hz.permit⟩,?_,?_⟩
   · obtain ⟨f,hf,hA⟩:= hh; exact ⟨f,hf,hA⟩
   obtain ⟨f,hf,hA⟩:= (ticket0 G n b).2.2.2; exact ⟨f,hf,hA⟩
-- OLD LIFE alignment labels exact, not comparing choices.
lemma leaves (n:Side)(W:PathData G)(c:Clip)(b:BudgetPoint)(β:ℝ)(M:Berry G θ) : let Z₁:=original n W c b β; let Z₂:=sketch n W c b β M
    Z₂.activities.E=Z₁.activities.E-toll n M c β ∧ Z₂.activities.K=Z₁.activities.K:=by
    intro O₀ X₀; refine ⟨?_,rfl⟩
    funext i; change stuff (upE (dictionary G n)) ((city M n b c β).regular) i=stuff _ _ i-stuff _ _ i
    by_cases he:i∈range (upE (dictionary G n))
    · obtain ⟨i,rfl⟩:=he; rw [stuffed,stuffed,stuffed]; rfl
    rw [blank _ _ he,blank _ _ he,blank _ _ he,sub_self]
lemma tollGate (hp: θ>2)(he:(Rose.payload M n c β).EBound b ε): Cash b (((O).activities.E,(O).activities.K)-((X).activities.E,(X).activities.K)) ε 0:=by rw [leaves _ _ _ _ _ M|>.1,leaves _ _ _ _ _ M|>.2]; change Cash _ (_-(_-_),(O).activities.K-(O).activities.K) _ _; rw [sub_self,sub_sub_cancel]; exact toll_cash hp he -- ambiguous kk
lemma masks (n:Side)(W: PathData G)(c:Clip)(b:BudgetPoint)(s:Signed)(x:Site n):∃ z,
   (∀ β, Apse.amid z (original n W c b β).activities s x) ∧ ∀ θ β (M:Berry G θ),Apse.amid z (sketch n W c b β M).activities s x:=by
   let J:= ℝ × (Option ((θ : ℕ) × Berry G θ))
   let U : J → Tap G n:= fun a=> match a.2 with | none => Start.payload c b G n a.1 | some M => city M.2 n b c a.1
   obtain ⟨u,h⟩:= Apse.roundish («P»:=b) W c (fun j=>j.1) (fun _=>0) (W:=U) (z:=⟨Tent.kinE n s x,Tent.kinK n s x⟩) (s:=s) (b:=x) (p:=Padded.sends (Start.reachAction s x)) («X»:=dictionary G n) (show ∀ j:J, Apse.duet _ _ _ _ _ _ from (by
           rintro ⟨β,_|⟨u,h⟩⟩ -- `none` rcases no binder convention
           · exact Tent.whirlN G b c n s x _
           exact Rose.spinning h b c s x β))
   exact ⟨u,fun β=> h (β,none), fun θ β M=> h (β,some ⟨θ,M⟩)⟩
variable (H:(original n W c b β).activities.Valid b v w)(hp: θ>2)(he:(payload M n c β).EBound b ε)
include hp he
lemma prices (h:Cash b ((O).activities.E,(O).activities.K) v w): (X).activities.Valid b (v+ε) w:=by
    have ht:=moveP h (toll_cash hp he); change Cash _ ((O).activities.E-toll n M c β,(O).activities.K-0) _ _ at ht; rw [sub_zero,add_zero,← leaves n W c b β M|>.1,← leaves n W c b β M|>.2] at ht
    have h' : issue b ((X).activities.E,(X).activities.K)=(X).activities:=rfl
    unfold Cash at ht; rw [h'] at ht; refine ⟨ht.1,ht.2.1,fun s x=>?_,ht.2.2.1,ht.2.2.2⟩; obtain ⟨u,h⟩:= masks n W c b s x; exact ⟨(h.2 θ β M).choose⟩
include H
lemma dry : (X).activities.Valid b (v+ε) w:= prices hp he (by unfold Cash; change (O).activities.RegularFamily b ∧ _; exact ⟨H.regular,H.forced,H.boundE,H.boundK⟩)
lemma totalRead (U:Config G n) : (O).exponent U+(KK).additive b U=(X).exponent U:=by
    have ht := dry H hp he; let E:=(O).activities; let E':=(X).activities; let f:=(KK); let S a:= (Real.exp a)^2
    have hh : f.additive b U= E.additive b U- E'.additive b U:= by
        unfold Activities.additive; rw [← ((Activities.ESeries H).summable U).tsum_sub ((Activities.ESeries ht).summable U)]; apply tsum_congr; intro i; unfold Activities.regularOccurrence; have he₁: E.reg i=E'.reg i:= rfl; have he₂:f.reg i=E'.reg i:= rfl; rw [he₁,he₂]; change masked _ (E'.reg i).support (toll n M c β i) U=_-masked _ (E'.reg i).support _ U; unfold masked Set.indicator ; split_ifs with h₁
        · rw [leaves n W c b β M |>.1]; change _=E.E i U-(E.E i U-_); ring
        ring
    change _+ f.additive b U=_; rw [hh]; unfold Rep.exponent; dsimp only [E,E',original,sketch,finish]; ring
-- absolute signs and orientation same. ∆v finite.
lemma tilt (U:Config G n) : (X).eval U= Real.exp ((KK).additive b U)*(O).eval U:=by
    rw [Rep.eval, Rep.eval,← totalRead H hp he U,Real.exp_add]; change _* _* (O).activities.gas (O).p _=_; ring -- gas same defeq
end joint
end YM.WilsonStartup.Rose
