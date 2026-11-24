import YM.OPE.Compatible.Grotto.Ramp
/-!
# Angular phase spectra.Lifting station members multilinearly. erased.B.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Filter Set ContinuousLinearMap Asymptotics
open scoped Topology BigOperators Classical
variable {d k i j s:ℕ}{E:Fin s→Type}{G:ℕ→Type}[∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)] [∀ i,NormedAddCommGroup (G i)] [∀ i,NormedSpace ℝ (G i)]
variable {b r x v u:ℝ}{μ:ℕ→ℝ}
local notation "S!"=> Mints E
local notation "L!"=> S! →L[ℝ] S!
variable {T:∀ i: Fin s,Cuts d μ v b (E i) G}
variable {p:(∀ i:Fin s,E i) →L[ℝ] (∀ i:Fin s,E i)}
open Drift
variable {H:Type}{L:H→ℕ→ Mints E→L[ℝ] Mints E}{W:Fin s→Type}{a w:H→ℝ}{f g:H→ℕ→ Mints E}
variable {P:ℕ→Mints E→L[ℝ] Mints E}{X:Mints E→L[ℝ] Mints E}
abbrev Yeast (H:Type)(P:H→ℕ→ Mints E→L[ℝ] Mints E)(X:S!→L[ℝ] S!)(a:H→ℝ)(u:ℝ):Prop:=TameP 1 a 1 P ∧ TameP u a 1 (fun i=>P i-Ford X)
-- packages
structure Eave (L:H→ℕ→Mints E→L[ℝ] Mints E)(X:S!→L[ℝ] S!)(T:(i:Fin s)→Cuts d μ v b (E i) G)(a:H→ℝ)(r θ u:ℝ)(k:ℕ):Prop where
     nonempty : 0<s
     fits : 1 ≤ a
     T1 : r*u≤θ
     T2 : 0 ≤ u
     Yi : Yeast H L X a u
     HB : Assist T X
     HP (i:H)(n:ℕ) : Assist T (L i n)
     mark : k < d
     slope (i:Fin s) : ShadeR (T i) k r
     chip (i:Fin s) : ShadeR (T i) (k+1) θ
namespace Eave
variable {θ:ℝ} -- ensure
variable (U:Eave L X T a r θ u k) -- T issue
include U
lemma ThetaPitch : 0 ≤ θ:= (T ⟨0,U.nonempty⟩).fast.trans (U.chip ⟨0,U.nonempty⟩|>.Fast.le)
lemma TonePitch : μ k < r:= (U.slope ⟨0,U.nonempty⟩).brisk k le_rfl U.mark
lemma trot : θ < μ k :=(U.chip ⟨0,U.nonempty⟩).slow _ (by omega)
lemma tier : θ ≤r:= (U.trot.trans U.TonePitch).le
lemma annex {J:Type}(z:J→ H): Eave (L∘z) X T (a∘z) r θ u k:= ⟨U.nonempty,fun i=> U.fits (z i),U.T1,U.T2,⟨appendP z U.Yi.1,appendP z U.Yi.2⟩,U.HB,fun j n=>U.HP (z j) n,U.mark,U.slope,U.chip⟩
-- read map into station
variable (j:H)
local notation "V!"=> Lingo r (L j)
local notation "F!"=> Fruition X (μ k)
lemma special : θ < r:=U.trot.trans U.TonePitch
variable [∀ i,CompleteSpace (E i)][∀ i,CompleteSpace (G i)][FiniteDimensional ℝ (G k)]
structure Oracles (F:V!→L[ℝ] F!): Prop where
     Ready (p:V!) : ∃ c,Hex θ (race (L j) 0 p.val - tale X (F p).val) c
-- uniqueness exp
omit [∀ i,CompleteSpace (E i)][∀ i,CompleteSpace (G i)][FiniteDimensional ℝ (G k)] in
lemma portion(w':Mints E)(z z':F!) (c c':ℝ)(hc: Hex θ (race (L j) 0 w' - tale X z.val) c)(hc': Hex θ (race (L j) 0 w' - tale X z'.val) c') :z=z':=by
     suffices hx:z-z'=0 by exact sub_eq_zero.mp hx
     refine Subtype.ext (show (z-z').val=(0:F!).val from ?_); apply Ipso (T:=X) (show _ from (show (Ux X (μ k)^s) (z-z').val=0 from (z-z').property)) U.trot U.ThetaPitch ⟨c'+c,?_⟩; apply (show (race (L j) 0 w' - tale X z'.val)-(race (L j) 0 w'-tale X z.val)= tale X (z-z').val from ?_) ▸ Hex.sub hc' hc; funext i; rw [Pi.sub_apply,Pi.sub_apply,Pi.sub_apply]; unfold tale; erw [map_sub]; abel
-- choose construct CL with section V.Wealth
lemma pipe : ∃ F:V!→L[ℝ] F!, ∀ p:V!,∃ c,Hex θ (race (L j) 0 p.val - tale X (F p).val) c:=by
    let z:V!→H:=fun _=>j; let U':= U.annex z; let f(p:V!):=p.val; have hf: Wealth f (a∘z) (fun p:V!=>‖p‖):=⟨1,zero_le_one,0,fun v=>by simp [f]⟩; have hx:(0:V!→ℝ) ≤ (fun p:V!=>‖p‖):=fun i=>norm_nonneg _
    obtain ⟨W,hW,hF,c,hc,hr⟩:= backFolks U'.fits hx U'.Yi.2 U'.HB U'.slope U'.T2 U'.mark U'.T1 U'.chip (sprint (L∘z) f) (speed U'.HP U'.fits hx U'.Yi.1 U'.slope f hf (fun i=>i.property)) fun _=>propel _ _; let Y(p:V!):F!:=⟨W p,hW p⟩; have hh(p:V!): Hex θ (race (L j) 0 p.val- tale X (Y p).val) (c p):= hr p
    let C:V!→ₗ[ℝ] F!:={ toFun:=Y,map_add':=fun x y=>by apply U.portion j (x+y).val _ _ _ (c x+c y) (hh _) ((show Hex θ _ _ from ?_)); apply (show (race (L j) 0 x.val-tale X (Y x).val)+(race (L j) 0 y.val-tale X (Y y).val)= _ from ?_) ▸ ((hh x).add (hh y)); funext i; simp only [Pi.sub_apply,Pi.add_apply,startEq]; unfold tale; erw [map_add,map_add]; abel,map_smul':=fun r x=>by apply U.portion j (r • x).val _ _ _ (‖r‖*c x) (hh _) (show Hex θ _ _ from ?_); apply (show r • (race (L j) 0 x.val-tale X (Y x).val)= _ from ?_) ▸ ((hh x).tint r); funext i; simp only [Pi.sub_apply,Pi.smul_apply,startEq]; unfold tale; erw [map_smul,map_smul]; exact smul_sub .. }
    obtain ⟨b,Hb,k,H⟩:= hF; exact ⟨C.mkContinuous (b*a j^k) (fun x=>H x),fun x=> ⟨_,hh x⟩⟩
noncomputable def PO : V! →L[ℝ] F!:= (U.pipe j).choose -- notation depends j
lemma taleF (p:V!) :∃ C,Hex θ (race (L j) 0 p.val - tale X (PO U j p).val) C:= (U.pipe j).choose_spec p
end Eave
end YM.OPE.Hark
