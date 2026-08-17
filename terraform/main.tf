# aws provider. tags everything with Project=proofbase so it is easy to find
provider "aws" {
    region = var.region
    default_tags {
        tags = {
            Project = "proofbase"
        }
    }
}

# use the account's default vpc and its subnets
data "aws_vpc" "default" {
    default = true
}

data "aws_subnets" "default" {
    filter {
        name = "vpc-id"
        values = [data.aws_vpc.default.id]
    }
}
