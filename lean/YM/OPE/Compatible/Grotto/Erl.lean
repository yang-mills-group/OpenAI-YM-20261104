import YM.OPE.Compatible.Grotto.Evo
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
variable {X:Mints E→L[ℝ] Mints E}(hA:1 ≤ a)(hw:0 ≤ w) (ht:TameP u a 1 (fun i=> L i-Ford X))
variable (Xh:Assist T X)(hr:∀ i,ShadeR (T i) k r)(hu:0 ≤ u)
variable {θ:ℝ} (hk:k<d)(he:r*u≤ θ)(hb:∀ i,ShadeR (T i) (k+1) θ)
include hA hw Xh hr hu hk he hb ht
variable [∀ i,CompleteSpace (E i)][∀ i,CompleteSpace (G i)][FiniteDimensional ℝ (G k)]
set_option maxHeartbeats 200000 in
lemma flavors (g:H→ℕ→Mints E)(hG:TameP r a w g)(hp:∀ i,Run (L i) (g i) 0)(i:ℕ)(hh:i<s)(p:H→ Mints E)(hL:∀ i,p i∈ Fruition X (μ k))(hp':Wealth p a w)(hT:TameK i θ a w (g-Vapor X p)):
     ∃ z:H→Mints E,(∀ i,z i∈Fruition X (μ k)) ∧ Wealth z a w ∧ TameK (i+1) θ a w (g - Vapor X z):=by
          let j:Fin s:=⟨i,hh⟩; let y:=g-Vapor X p; let f(i:H)(n:ℕ):= L i n (g i n)- X (g i n)
          have h₁:= (T j).tempo k hk; have hx:= (hr j).brisk k le_rfl hk; have hq:θ < μ k:= (hb j).slow k (by omega); have hθ:0≤θ:= (T j).fast.trans (hb j).Fast.le; have hf(x):Run (Ford X) (y x) (f x):= periodZ hp X p x; have hy:TameP θ a w f:= Trade ht hu (h₁.trans hx).le he hG; have hu': TameP r a w y:= TameP.sub hA hw hG (pureW (μ k) h₁.le hx p hL hp')
          let Q:H→ℕ→E j:= Busy (fun _=> Ford X) y j+fun i n=> f i n j; have hQ : TameP θ a w Q:= TameP.plus hA hw (Busy.toll j (fixedT X a) hA hw hT) (TameP.cast (proj j) hy); let Y:=fun i n=> y i n j; let Z:= stride X j; have hY(x):Run (Ford Z) (Y x) (Q x):=eleg (fun _ _=>Xh.arum) x j (hf x)
          obtain ⟨c,hc,hC⟩:= hQ; obtain ⟨B,h,H'⟩:= solk (T j) (hb j).Fast (hb j).ex 0 (by omega); choose t ht hT' using fun x=> H' (Ford Z) (fun _=> Xh.gait j) (Q x) _ (hC x) (fun i=>(T j).first _); let P:=fun x=>race (Ford Z) (Q x) (t x); have hV:TameP θ a w P:= ⟨fun i=>B*c i,scaleD hc,hT'⟩; let V:=Y-P
          have hBy(x):Run (Ford Z) (V x) 0:= (sub_self (Q x)) ▸ Run.sub (hY x) (gait _ _ _); have hC:TameP r a w V:=TameP.sub hA hw (TameP.cast (proj j) hu') (hV.grows hθ (hq.trans hx).le); let w₀(x:H):=(T j).Tap k (V x 0) -- params
          have hX(x): V x 0∈ (T j).flag k:=by obtain ⟨a,b,c⟩:=hC;exact inLayer (hr j|>.Fast) (fun _=> Xh.gait _) (hBy _) (Nat.le_of_lt hk) (hr j|>.slow) (c x) -- line fix
          obtain ⟨A,hF⟩:= tintCan T Xh hk hb j; let W:= A ∘ w₀; have hs(x): W x∈ KernNut X (μ k) i ∧ (T j).Tap k ((W x) j)=w₀ x:= hF (w₀ x); have hω:Wealth W a w:= aimW A (aimW _ (hC.place 0)); let c:= Vapor X W
          have ha:∀ i,Run (Ford Z) (fun n=> c i n j) 0:=fun i=> runT (fun _=> Xh.arum) (TALE X (W i)) j ((hs i).1.2); let d:=V-(fun i n=> c i n j); have hv:TameP θ a w d:=by
              obtain ⟨u,H,Ht⟩:= even (T j) (hb j).Fast (hb j).ex (k+1) (hb j).slot (hb j).brisk; have hx:Wealth (fun i=>d i 0) a w:=subW hA hw (hC.place 0) (aimW (proj j) hω); refine ⟨_,scaleD (k:=u) (normW hx),fun x=>?_⟩; apply Ht (Ford Z) (fun _=> Xh.gait j) _ (sub_zero (0:ℕ→E j) ▸ Run.sub (hBy x) (ha x)); apply ((T j).next _ hk _).2; refine ⟨((T j).flag k).sub_mem (hX x) (phaseLeaf T Xh hk j (W x) ((hs x).1.1) ((hs x).1.2)),?_⟩; change (T j).Tap k (V x 0-W x j)=0; rw [map_sub,(hs x).2]; exact sub_self _
          refine ⟨p+W,fun x=> (Fruition _ _).add_mem (hL x) ((hs x).1.1),fortSum hp' hω hA hw,?_⟩; rw [filings,←sub_sub]; intro k hk'; by_cases he:k=j; swap
          · have hb:k.val < i:=by have h0 : k.val≠i:=Fin.val_injective.ne he;omega
            have hx(x n) : ((g-Vapor X p)-c) x n k=y x n k:=by rw [Pi.sub_apply,Pi.sub_apply,Pi.sub_apply,show c x n k=0 from followPow Xh.arum _ i _ ((hs x).1.2) _ hb,sub_zero]
            exact (show (fun x n=>((g -Vapor X p)-c) x n k)=fun x n=>y x n k from funext fun x=>funext fun t=> hx _ _).symm ▸ hT k hb
          subst k; apply (show (fun x n=>(y-c) x n j)= d+P from funext fun x=> funext fun n=>?_ ) |>.symm ▸ (TameP.plus hA hw hv hV)
          change y x n j-c x n j= y x n j- P x n- c x n j+ P x n; abel
lemma backFolks (g:H→ℕ→ Mints E)(hG:TameP r a w g)(hp:∀ i,Run (L i) (g i) 0):∃ x:H→Mints E,(∀ i,x i∈Fruition X (μ k))∧ Wealth x a w∧ TameP θ a w (g - Vapor X x):=by
     have he'(i:ℕ)(hx:i≤s):∃ x:H→Mints E,(∀ i,x i∈Fruition X (μ k))∧ Wealth x a w∧ TameK i θ a w (g - Vapor X x):=by
          induction i with
          | zero=> exact ⟨0,fun i=> (Fruition _ _).zero_mem,wealthZ _ _,fun j h=>by omega⟩ -- auto
          | succ n ih=> obtain ⟨q,hQ,hx',hf⟩:= ih (by omega); exact flavors hA hw ht Xh hr hu hk he hb g hG hp n hx q hQ hx' hf
     obtain ⟨x,hx,hT',hG'⟩:=he' s le_rfl; exact ⟨x,hx,hT',TameK.all hG' hA hw⟩
end YM.OPE.Hark
