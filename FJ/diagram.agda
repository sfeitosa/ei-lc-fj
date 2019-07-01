open import Data.Nat
open import Data.Fin
open import Data.List using (List ; map)
open import Data.List.All using (All)
open import Data.Vec using ([]; _∷_)
open import Data.Product using (_×_ ; proj₁ ; proj₂)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Any using (here ; there)
open import Relation.Binary.PropositionalEquality using (refl)

import etfj
import itfj renaming (Ctx to ICtx)

module diagram (n : ℕ) where

-- Object is represented by 0
module FJ = etfj 0
-- We have 'n' classes
module IFJ = itfj n

open FJ 
open IFJ 

-- Elaborating types

postulate 
  Ty⇒Name : Ty → Name
  Name⇒Ty : Name → Ty

-- Elaborating context

elabCtx : Ctx → ICtx
elabCtx Γ = map (λ v → Name⇒Ty (proj₂ v)) Γ

-- Elaborating class table

open FJ.ClassTable
open IFJ.ClassTable

elabMSig : Meth → MSig
elabMSig m = record { ret = Name⇒Ty (Meth.ret m) ; params = map (λ p → Name⇒Ty (proj₂ p)) (Meth.params m) }

elabFlds : List (Name × Name) → List Ty
elabFlds flds = map (λ f → Name⇒Ty (proj₂ f)) flds

elabMSigs : List (Name × Meth) → List MSig
elabMSigs meths = map (λ m → elabMSig (proj₂ m)) meths

elabCSig : Class → CSig
elabCSig c = record { flds = elabFlds (Class.flds c) ; signs = elabMSigs (Class.meths c) }

postulate
  elabCT : CT → CTSig

-- Elaborating expression

postulate
  Δ : CT

open FJ.Syntax
open FJ.Typing Δ
open FJ.Auxiliary Δ
open IFJ.Syntax (elabCT Δ) renaming (Expr to IExpr)

elabVar : ∀ {Γ x c} → Γ ∋ x ∶ c → Name⇒Ty c ∈ elabCtx Γ
elabVar here = here refl
elabVar (there wtv) = there (elabVar wtv)

--elabField : ∀ {f c} → (flds : List (Name × Name)) → flds ∋ f ∶ c → Name⇒Ty c ∈ {!!}
elabField : ∀ {Δ Γ e C flds f c} → Γ ⊢ e ∶ C → FJ.Auxiliary.fields Δ C flds → flds ∋ f ∶ c → Name⇒Ty c ∈ IFJ.Auxiliary.fields (elabCT Δ) (Name⇒Ty C)

elabMeth : ∀ {Δ Γ e C cd m md} → Γ ⊢ e ∶ C → Δ ∋ C ∶ cd → Class.meths cd ∋ m ∶ md
        → mkSig (Name⇒Ty (Meth.ret md)) (map (λ p → Name⇒Ty (proj₂ p)) (Meth.params md)) ∈ IFJ.Auxiliary.signatures (elabCT Δ) (Name⇒Ty C) 

elabExpr : ∀ {Γ e τ} → Γ ⊢ e ∶ τ → IExpr (elabCtx Γ) (Name⇒Ty τ)
elabExprs : ∀ {Γ es MD} → Γ ⊧ es ∶ proj₂ (Data.List.unzip (Meth.params MD)) → All (λ n → IExpr (elabCtx Γ) (Name⇒Ty n)) (proj₂ (Data.List.unzip (Meth.params MD)))

elabExpr (T-Var x) = Var (elabVar x)
elabExpr (T-Field {flds = flds} wte wtf f) = Field (elabExpr wte) (elabField wte wtf f) 
elabExpr (etfj.Typing.T-Invk wte (this cd md) mp) = Invk (elabExpr wte) (elabMeth wte cd md) {!!}
elabExpr (T-New {C = C} flds wtcp) = New (Name⇒Ty C) {!!}
