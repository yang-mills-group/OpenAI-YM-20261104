import YM.MSbar.Cypress.Twig
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Cypress
open Function Filter Whisk Lis Measuring Cacao Push Uniform Lattice RG Tonic Aqua
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Lapaz
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal
variable {σ:Type} [Fintype σ]
local notation "π"=> PowerSeries.coeff
structure Locks (F f : List σ→ℝ)(B P:List σ→PowerSeries ℝ)(p g:List σ→ℝ) :Prop where
    f0:F []=1
    p0:B []=1
    v0:p []=0
    lens (L:List σ)(i:σ):F (L++[i])= Yarn L.length (fun u:List Bool=> F (takeout true u L)*f (takeout false u L++[i]))
    book (L:List σ)(i:σ):B (L++[i])= Yarn L.length (fun u:List Bool=> B (takeout true u L)*P (takeout false u L ++ [i]))
    mark (L:List σ)(i:σ):p (L++[i])= Yarn L.length (fun u:List Bool=> p (takeout true u L)*π 0 (P (takeout false u L++[i]))+ π 0 (B (takeout true u L))*g (takeout false u L++[i]))
noncomputable def tape (A K B x ε t:ℝ)(p:ℕ):= ε*(A+B+x)+(K+B)*x+t*A*B+B^2+t*K*B+t^(p+1)*(K*A)
variable {t P S Y X k0 ε:ℝ}{p j m:ℕ}
lemma pricing (F f d e:ℝ)(V B:PowerSeries ℝ)(p:ℕ)(ht:0≤t)(hv:t≤1)(hP:Belt p V ≤ P)(hk:Belt p B ≤ k0)(hd:|d|≤Y)(he:|e|≤Y)(hF:|F-taste p V t-d|≤ ε)(hg: |f-taste p B t-e|≤ X):
        |F*f-taste p (V* B) t-(d*π 0 B+ π 0 V*e)|≤ tape k0 P Y X ε t p:=by -- parameters order verify
    let x:=taste p V t; let y:=taste p B t; let u:=F-x-d; let v:= f-y-e; let b:=π 0 V; let a:=π 0 B
    have hx: |x|≤ P:= (taste_pays ht hv V).trans hP; have hy:|y|≤ k0:=(taste_pays ht hv B).trans hk; have hu:0≤P+Y:=by apply add_nonneg ((abs_nonneg _).trans hx) ((abs_nonneg _).trans hd)
    have hX:0≤ X:=(abs_nonneg _).trans hg; have hY:0 ≤ Y:=(abs_nonneg _).trans he; have hZ:0 ≤ ε:= (abs_nonneg _).trans hF; have hN:0 ≤ P:=(Belt_pos ..).trans hP
    have hr:|f| ≤ k0+Y+X:=by refine (le_of_eq ?_).trans ((abs_add_le ..).trans (add_le_add ((abs_add_le y e).trans (add_le_add hy he)) hg)); congr 1; unfold y; abel
    rw [show _*f- _ - _ = u*f + (x+d)*v + d*(y-a)+d*e+(x-b)*e+(x*y-taste p (V*B) t) from ?_]
    · have he0 : |x*y-taste p (V*B) t| ≤ t^(p+1)*(P*k0):=by rw [abs_sub_comm]; apply (taste_mul ..).trans; apply mul_le_mul_of_nonneg_left (mul_le_mul hP hk (Belt_pos ..) hN) (pow_nonneg ht _); exact ht;exact hv -- args
      refine (abs_add_le ..).trans (add_le_add ((abs_add_le ..).trans (add_le_add ((abs_add_le ..).trans (add_le_add ((abs_add_le ..).trans (add_le_add ((abs_add_le ..).trans (add_le_add ?_ ?_)) ?_)) ?_)) ?_)) he0)
      · exact (abs_mul ..).trans_le (mul_le_mul hF hr (abs_nonneg _) hZ)
      · exact (abs_mul ..).trans_le (mul_le_mul ((abs_add_le x d).trans (add_le_add hx hd)) hg (abs_nonneg _) hu)
      · rw [abs_mul]; exact (mul_le_mul hd ((sauce B p ht hv).trans (mul_le_mul_of_nonneg_left hk ht)) (abs_nonneg _) hY).trans_eq (by ring)
      · rw [abs_mul]; exact (mul_le_mul hd he (abs_nonneg _) hY).trans_eq (by ring)
      rw [abs_mul]; exact mul_le_mul ((sauce V p ht hv).trans (mul_le_mul_of_nonneg_left hP ht)) he (abs_nonneg _) (mul_nonneg ht hN)
    unfold u v b a x y;ring
-- Yarn cash recurrence εstep.Truncated order all.Wallet
noncomputable def coins (C D b ε t:ℝ)(p n:ℕ) := match n with | 0=>0|n+1=> let v:= coins C D b ε t p n; v+ε+ 2^n*tape C D b v ε t p
variable {F f h g:List σ→ℝ}{T W:List σ→PowerSeries ℝ}
local notation "µ"=>PowerSeries.coeff
lemma holt (p:ℕ)(t:ℝ):∃ F: PowerSeries ℝ→+ℝ,∀ x,F x=taste p x t:=⟨{toFun:=fun x=>taste p x t,map_zero':=by simp [taste],map_add':=fun _ _=>taste_add ..},fun x=>rfl⟩
section
variable (H:Locks F f T W h g) (ht:0≤t)(hc:t≤1)(L:List σ)(hp:L.length ≤ m)
    (hK:∀ v:List σ,v⊆ L→v.length≤ m→Belt p (T v) ≤ P)
    (hF:∀ v:List σ,v⊆ L→v.length≤ m→ |F v-taste p (T v) t-h v| ≤ ε)
    (hg:∀ v:List σ,v⊆L→v.length ≤ m → v≠[]→ Belt p (W v) ≤ S ∧ |g v| ≤ Y)
    (hh:∀ v:List σ,v⊆L→v.length ≤ m→ |h v| ≤ Y)
variable (hs:0 ≤ S)
local notation "τ"=> taste p
local notation "δ!" i=> coins S P Y ε t p i
include ht hc H hK hF hg hh hs
lemma values (n:ℕ) :∀ v:List σ,v⊆L→v.length≤ n → v.length≤ m → v≠ []→ |f v-taste p (W v) t-g v| ≤ δ! n:=by
    have hb:0≤ P:=(Belt_pos ..).trans (hK [] (by simp) (by simp)); have he:0≤ ε:= (abs_nonneg _).trans (hF [] (by simp) (by simp)); have hY : 0 ≤ Y:=(abs_nonneg _).trans (hh [] (by simp) (by simp))
    have hh0(i:ℕ) : 0≤ δ! i:=by induction i with|zero=>exact le_rfl|succ i ih=>rw [coins]; unfold tape;positivity
    induction n with
    | zero=> intro v _ hp _ h; exact False.elim (h (List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hp)))
    | succ k ih=>
       intro v hv hl hm hg'; by_cases h':v.length ≤ k -- shadow h.C.
       · rw [coins]; let d:= δ! k; apply (ih v hv h' hm hg').trans; have ht':0≤ d:=hh0 k; have hT:0 ≤ tape S P Y d ε t p := by unfold tape; positivity
         exact (le_add_of_nonneg_right he).trans (le_add_of_nonneg_right (mul_nonneg (pow_nonneg (by norm_num) _) hT))
       have hL : v.length=k+1:=by omega
       obtain ⟨s,i,rfl⟩:∃ s:List σ,∃ i:σ,v=s++[i]:=⟨v.dropLast,v.getLast hg',(List.dropLast_append_getLast hg').symm⟩
       rw [List.length_append,List.length_cons,List.length_nil] at hL; have hp: s.length=k:=Nat.add_right_cancel hL; let U:=s++[i]
       let A(u):=takeout true u s; let B(u):=takeout false u s++[i]; let Q(v):= F v - τ (T v) t- h v -- collision
       let P'(u):= F (A u)*f (B u) - taste p (T (A u)* W (B u)) t - (h (A u)*µ 0 (W (B u))+µ 0 (T (A u))*g (B u));
       obtain ⟨E,hE⟩:=holt p t; have hQ: Q U= Yarn s.length P' :=by
            unfold Q U; rw [H.lens,H.book,H.mark, ← hE,Whisk.spun]; simp_rw [hE]; unfold P' A B; apply sub_eq_iff_eq_add.mpr; rw [sub_eq_iff_eq_add,←pockets,← pockets]; apply stitch; intro v hv; abel -- goal
       let R:=fun l:List Bool=>if true ∈ l then P' l else 0; let M:= f U - τ (W U) t-g U;
       have hz(v:List Bool)(hn:true∉v)(hy:v.length=s.length):P' v=M:=by
             obtain ⟨hx,ht⟩:= takeout_ghost s hy hn; unfold P' M U A B; rw [ht,hx,H.f0,H.p0,H.v0,one_mul,one_mul,show PowerSeries.coeff 0 (1:PowerSeries ℝ)=1 from (by simp),one_mul,zero_mul,zero_add] -- name
       have hP: Q U=M+Yarn s.length R:=by
             rw [hQ,← alone]; exact stitch _ fun v hv=>by split_ifs with he; exact rfl; exact hz v he hv -- missing branch
       have hu(v:List Bool)(he:v.length=s.length)(hV:true∈v): |P' v|≤ tape S P Y (δ! k) ε t p:=by
              have ht':(A v).length ≤ s.length:=(sunset true v s he).trans_le ((part_le ..).trans_eq he); have hK1 : (B v).length ≤ k:=by unfold B; simp only [List.length_append,List.length_cons,List.length_nil]; have hx:=streak s v he hV; omega
              have hz1 : (A v) ⊆ L:=List.Subset.trans (List.Subset.trans (Bout.narrow ..) (by simp)) hv; have hz2 : B v ⊆ L:= List.Subset.trans (by unfold B; grind [Bout.narrow]) hv -- edit
              have hu1 : (A v).length  ≤ m:= by omega
              have hu2:(B v).length  ≤ m:=by omega
              have he₂:=hg (B v) hz2 hu2 (by simp [B]);
              exact pricing _ _ _ _ _ _ p ht hc (hK _ hz1 hu1) he₂.1 (hh _ hz1 hu1) he₂.2 (hF _ hz1 hu1) (ih _ hz2 hK1 hu2 (by simp [B]))
       change |M| ≤ _; let b:= tape S P Y (δ! k) ε t p; have hx:0 ≤ b:=by unfold b tape; have ht:=hh0 k; positivity
       rw [eq_sub_of_add_eq hP.symm]; refine ((abs_sub ..).trans (add_le_add (hF U hv hm) ((polished ..).trans ((shiny _ (g:=fun _=> b) (fun i hi=>?_)).trans_eq (total_books ..))))).trans ?_ -- goals order
       · unfold R; split; exact hu i hi (by assumption); rw [abs_zero]; exact hx
       rw [hp,Fintype.card_bool,Nat.cast_ofNat,coins]; exact add_le_add_left (le_add_of_nonneg_left (hh0 k)) _
end
end YM.MSbar.Cypress
