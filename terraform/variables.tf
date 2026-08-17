variable "region" {
    default = "us-east-2"
}

variable "db_name" {
    default = "proofbase"
}

variable "db_username" {
    default = "proofbase"
}

# no default. set in terraform.tfvars, which deploy.sh also reads
variable "db_password" {
    type = string
    sensitive = true
}

# who can attempt to ssh in. 0.0.0.0/0 is ok for now
variable "ssh_cidr" {
    default = "0.0.0.0/0"
}

variable "public_key_path" {
    default = "~/.ssh/id_ed25519_proofbase.pub"
}
