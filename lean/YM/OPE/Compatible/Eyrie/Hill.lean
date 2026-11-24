import YM.OPE.Compatible.Niche.Chop
import YM.Push.GRID_APPROXIMATION.Iterate
import YM.Corona.Spend
import YM.Work.E08
import YM.Push.RELAY_MARK.Micro
/-!
# Local (outside) nullity under the actual shared tag kernel, complete estimates

Polynomial control here not needed. Work at fixed cutoff level k, tori stay arbitrary.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Eyrie
open Function Filter MeasureTheory Spec Lattice RG Wilson Source Cov Allot MergeProof Next.Extract Dash Analysis Extra.Histories Next.Rank
open Push.GridApprox Push.Mark
open scoped Topology BigOperators Classical
variable {d k m N p M:ℕ}{o:Side}{G:Gauge}(A:History G)(h:A.Selected)
local notation "T!"=> A.levels.clock
abbrev lots (G:Gauge)(n: Side):= Config G n→ℂ
noncomputable def rim (s n:ℕ):= n+40*(s+10)
noncomputable def fleet (m n:ℕ):= rim ((T!).J m) n
set_option maxRecDepth 4096 in
lemma upperWin (k p r:ℕ)(x:Site (A.S.side k p))(hp:x ∈ Outer (fleet A k r) 0) : let S:=(T!).op k p; Push.GridApprox.window (S.ratio.embed x) (Push.GridApprox.reach S.patch) ⊆ Outer (fleet A (k+1) r) 0:=by
        intro S y hy; let s:=(T!).J k; let i:=(T!).J (k+1); let L:=S.patch.L.val
        have hL:3 ≤ L:= S.patch.coarse; obtain ⟨u,hu,rfl⟩:=hy
        let x':=S.ratio.embed x; let y:=wrap _ u+x'; have hz: separation x' y  ≤  10*((i+3)*L):= Work.E08.separation_box_add x' (show _∈box _ from hu); have he:=Corona.below S.ratio x 0; rw [Motion.embed_origin] at he
        let v:=separation x' 0; let w:=separation x 0; let W:=separation y 0; change L*w  ≤  v at he; have hi:i ≤ s+1:=A.levels.fits.stepSlow _
        change r+40*(s+10)<w at hp; change r+40*(i+10)< W
        have hb : v  ≤  10*((i+3)*L) + W:= (separation_triangle x' y 0).trans (Nat.add_le_add_right hz _)
        have hv:30*s+r+360 < w-(10*(i+3)) := by omega
        have hB : L*(w-10*(i+3))  ≤  W:= by
               have ha: 10*(i+3)+(w-10*(i+3))=w:=by omega
               have hh:= he; nth_rw 1 [← ha,mul_add] at hh; rw [show L*(10*(i+3))=10*((i+3)*L) from by ring] at hh; omega
        have hh:= Nat.mul_le_mul hL (show 30*s+r+360  ≤  _ from hv.le); omega
variable (hk:k ≤ m){J:lots G (A.S.side k p)}
lemma seals {n:ℕ}(hk:k ≤ m)(hS:LocalOn (Outer (fleet A k n) 0) J) (ht: RG.Envelope J):LocalOn (Outer (fleet A m n) 0) (Push.GridApprox.backTo A N p hk J):=by
        induction m,hk using Nat.le_induction with
        | base=> rwa [backTo_self]
        | succ m hk ih=> rw [backTo_next A N p hk]; exact Push.GridApprox.back_local (A.levels.blocks ..|>.branches) (backTo_env A N p hk ht) ih _ _ (fun x hx=> upperWin A m p n x hx)
local notation "β!"=> A.β N p N
noncomputable def illum (b:ℝ)(F:lots G o):lots G o:= fun i=> (bare b i:ℂ)*F i
lemma lite {b:ℝ} (J:lots G o)(hv:Continuous J):Continuous (illum b J):= (Complex.continuous_ofReal.comp (bare_cont ..)).mul hv
variable (G1:Gauge)
noncomputable def πfee (F:lots G o)(J:lots G o):ℂ:= ∫ x,F x*J x ∂prior G o
noncomputable def γfee (J:lots G o):ℝ:= ∫ x,‖J x‖ ∂prior G o
-- point-source null metric uses absolute rather than relative Haar masses
noncomputable def puff (N p:ℕ) {k:ℕ} (d:ℕ)(H:lots G (A.S.side N p))(hk:k ≤ N):lots G (A.S.side k p):=(A.S.a k:ℂ)^d • Push.GridApprox.pushTo A N p hk (illum (A.β N p N) H)
lemma microK (f:Pre G)(hc:Continuous f)(hM: MicroAt f d M)(hu:M  ≤ (A.S.side N p).val)(hn:(β!)≠0)(hp:k ≤ N)(l:ℕ)(hv:LocalOn (Outer (fleet A k d) 0) J)(he:Envelope J): πfee (puff A N p l (f∘expandAt 0) hp) J=0:=by
        let T:= f∘expandAt (0:Site (A.S.side N p)); let W:=backTo A N p hp J
        have hJ:=backTo_env A N p hp he; have ht:Continuous T:=Push.Mark.onStencil _ hc
        have hm: LocalOn (Outer d 0) W:= by
                have hz : d ≤ fleet A N d:= Nat.le_add_right ..; have hh:= seals A (N:=N) hp hv he; exact fun i j hp=> hh i j (agrees_mono hp (fun _ hx=> hz.trans_lt hx))
        have hh:= hM _ hu 0 (β!) hn W hm hJ; change moment _ (T*W)=0 at hh
        rw [moment_formula _ (T*W) (((Envelope.compactC ht).mulC hJ).integrableC _)] at hh
        have hx:= (mul_eq_zero.mp hh).resolve_left (inv_ne_zero (Complex.ofReal_ne_zero.mpr (partition_pos _).ne'))
        unfold πfee puff; simp only [Pi.smul_apply, smul_eq_mul,mul_assoc,integral_const_mul]; rw [pushTo_dual A N p hp he _ ((lite T ht).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]; unfold illum; simp_rw [mul_assoc]; rw [show (∫ x, (bare (β!) x:ℂ)*(T x*backTo A N p hp J x) ∂prior G (A.S.side N p)) = 0 from hx]; exact mul_zero _
end YM.OPE.Eyrie
