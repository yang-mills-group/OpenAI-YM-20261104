import YM.PertExtension.TopCalibration
import YM.PertExtension.HuePanel

/-! Off-shell jet read of the finite lifted slot polynomial. -/
set_option autoImplicit false
set_option maxHeartbeats 1050000
noncomputable section
namespace YM.PertExtension.Heat.Ray
open Function Set Filter Finset RG Wilson Lattice Labels Source Drops Hue MvPolynomial
open Next.Rank Next.Rank.Beamer Next.Rank.Configuration Next.Rank.LiftMark Next.Rank.Normal Next.Rank.Spindle Top Push.CutoffProjectors Next.Foundations
open scoped Topology ContDiff Classical BigOperators
variable {G:Gauge}{d:ℕ}
local notation "V"=> Panel RG.Slot G

def address (i : V):Address G := ⟨i.1.offset,i.1.plaq,i.2⟩

def print (d:ℕ) : Hue.Poly RG.Slot G→ₐ[ℂ] Pol G:= (rename (Subtype.val : KeyIn G d → _)).comp (exchange (ink d address))
lemma printed (p:poly V)(J:Snap G d) : aeval (kp d J) (exchange (ink d address) p)= Spindle.text (fun i:V=>glow J i.1 i.2) p:=by
 apply DFunLike.congr_fun (f:=(aeval (kp d J)).comp (exchange (ink d address))); ext1 i
 simp only [Spindle.text,AlgHom.comp_apply,glyph,exchange_x,ink,_root_.map_sum,Finsupp.linearCombination_single,map_smul,aeval_X]
 change _ = ((oneGlow d J (i.1.offset,i.1.plaq) i.2:ℝ):ℂ)
 rw [traffic,Complex.ofReal_sum];refine Finset.sum_congr rfl fun j _=>?_ ; rw [Complex.ofReal_mul,kp_real];exact mul_comm ..
lemma display_jet (p:poly V)(J:Jet G) : Labels.read J (print d p)= Spindle.text (fun i:V=>glow (Drops.trunk d J) i.1 i.2) p:=by
   rw [← printed,print,AlgHom.comp_apply];unfold Labels.read;rw [aeval_rename];congr 2;funext i; have ht:= i.property
   simp only [kp,Function.comp_apply,Labels.coord,expand,Drops.trunk, dif_pos (show i.val.1< d-1 from (spanKey d i).isLt)] -- adjust
lemma same_power (p:poly V)(J:Jet G)(s:ℝ): symbolEval (d:=d) p J s = Labels.read (scaleJet J s) (print d p):=by unfold symbolEval;rw [display_jet]

abbrev clipped (d)(p : poly V):= capRead d (print d p)

lemma before_tests (j : Lens G d)(p:poly V) : testLM p j = (j.2.val.factorial:ℝ) • read j.1 (tier j.2.val (print d p)) := by
  change iteratedDeriv _ _ _ = _; simp_rw [same_power];exact deriv_read ..
lemma weigh (p :Pol G) : Rise.trim p Labels.generation d=capRead d p:= by ext i; rw [Rise.trim_coeff,coeff_capRead];rfl
lemma probeX {D:ℕ}(h:d≤D)(i:V): Rise.trim (print D (X i)) Labels.generation d= ∑ k:KeyIn G d, (↑(Beamer.tester k.val (address i):ℝ):ℂ) • X k.val:=by
 unfold print; rw [AlgHom.comp_apply,exchange_x];simp only [Normal.glyph,ink,map_sum,Finsupp.linearCombination_single,map_smul,rename_X];
 change (level Labels.generation d) _ = _
 rw [map_sum];simp_rw [map_smul]
 let A:= univ.filter (fun i:KeyIn G D=> generation i.val≤d)
 let f (k:Key G):Pol G:= ((Beamer.tester k (address i):ℝ):ℂ) • X k
 calc
    _ = ∑ k∈A, f k.val:= by
      unfold A f; rw [sum_filter];refine Finset.sum_congr rfl fun i hi=>?_;change _ • Rise.trim _ generation _= _
      rw [X,trim_mono,Finsupp.weight_single];simp only [one_smul];split_ifs <;> simp
    _ = _ := by
      exact sum_bij (fun i hi=> (⟨i.val, (mem_filter.mp hi).2⟩:KeyIn G d)) (fun i h=>mem_univ _) (fun a ha b hb h=>Subtype.ext (congr_arg (Subtype.val : KeyIn G d → Key G) h)) (fun b hb=>⟨⟨b.val,b.property.trans h⟩,by simp [A,b.property],rfl⟩) (fun i hi=>rfl)
lemma bounded_test {d':ℕ}(h:d≤d')(j : Lens G d)(p:poly V) :
       (j.2.val.factorial:ℝ) • Labels.read j.1 (tier j.2.val (print d' p)) = testLM p j := by
    rw [before_tests,← tier_capRead d _ _ (by omega), ← weigh, verdict_map d _ (Q:=print d) (fun i=>(probeX h _).trans (probeX (d:=d) le_rfl i).symm),weigh,tier_capRead d _ _ (by omega)]

end YM.PertExtension.Heat.Ray
