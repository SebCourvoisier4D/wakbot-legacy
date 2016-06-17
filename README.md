# wakbot-legacy

## Prérequis

* *Java SDK 6* et *Apache Maven*
* *Perforce* avec un compte et un workspace à jour
* Une build stable de *Wakanda Server*
* *Firefox*
* *Chrome*
* *PhantomJS*
* *Sikuli*

Voir https://project.wakanda.org/projects/development/wiki/WakBot_Setup pour les détails d'installation de l'ancien système.

## Installation

* `npm install`
* Copier le fichier `config/sample-<os>.config.json` correspondant à la configuration et le renommer `config/localhost.config.json`
* Editer le fichier `config/localhost.config.json` et renseigner/adapter les différents paramètres requis (se référer à https://project.wakanda.org/projects/development/wiki/WakBot_Setup#Configuration). Laisser la valeur "main" pour le paramètre `WAKANDA_BRANCH`
* Créer un dossier `0` dans le dossier pointé par le paramètre `BUILD_TEST_DIR` et y poser un Server et un Studio
* Veiller à ce que le workspace Perforce soit à jour pour les tests (`//depot/Wakanda/main/Common/tests/`, `//depot/Wakanda/main/Server/tests/` et `//depot/Wakanda/main/Studio/tests/`)

## Utilisation

Voir https://project.wakanda.org/projects/development/wiki/WakBot_Usage, remplacer `node WAKBOT` par `npm test`.

Par exemple : `npm test server_ssjs_api_file_*`, `npm test server_waf_api_ds_*`, etc.

